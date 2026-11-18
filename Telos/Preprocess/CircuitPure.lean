import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Rewriter.Rewrite

/-!
# The circuit propagator, without proofs

The propagation of `CircuitPropagator.lean` (cvc5's `CircuitPropagator`), in
the same order and with the same results, but without building facts. Each
assignment records why it was made (`Reason`): an assertion, a parent whose
value forces it (backward), or the values of its children (forward). Non-clausal
simplification justifies the learned literals by replaying this trace
(`SemProc.learn`, `Telos/Core/Learn.lean`), with one check for every case: the
three-valued value of the connective.
-/

namespace Telos.Preprocess

open Node

inductive Reason where
  /-- An assertion. -/
  | root
  /-- Forced by the value of the parent, the trace item of that index. -/
  | bwd (parent : Nat)
  /-- Forced by the values of its children. -/
  | fwd

structure TraceItem where
  node : Node
  value : Bool
  reason : Reason

structure CPPState where
  /-- The value of each assigned node, and its index in the trace. -/
  assign : Std.HashMap Key (Bool × Nat) := {}
  queue : Array Node := #[]
  backEdges : Std.HashMap Key (Array Node) := {}
  seen : Std.HashSet Key := {}
  trace : Array TraceItem := #[]
  /-- The learned literals, as trace indices. -/
  learned : Array Nat := #[]
  conflict : Bool := false

abbrev CPP := StateM CPPState

namespace CPP

def valueOf (n : Node) : CPP (Option Bool) := do
  return ((← get).assign.get? ⟨n⟩).map (·.1)

def indexOf (n : Node) : CPP (Option Nat) := do
  return ((← get).assign.get? ⟨n⟩).map (·.2)

def isAssignedTo (n : Node) (v : Bool) : CPP Bool := do
  return (← valueOf n) == some v

/-- `assignAndEnqueue`. -/
def assign (n : Node) (v : Bool) (r : Reason) : CPP Unit := do
  if (← get).conflict then return
  if let .const (.boolean b) := n then
    if b != v then modify fun s => { s with conflict := true }
    return
  match ← valueOf n with
  | some w => if w != v then modify fun s => { s with conflict := true }
  | none =>
    modify fun s =>
      let i := s.trace.size
      let tr := s.trace
      let a := s.assign
      let q := s.queue
      let s := { s with trace := #[], assign := {}, queue := #[] }
      { s with trace := tr.push ⟨n, v, r⟩, assign := a.insert ⟨n⟩ (v, i), queue := q.push n }

/-- The backward reason from `parent`. -/
def bwdOf (parent : Node) : CPP Reason := do
  return .bwd ((← indexOf parent).getD 0)

def computeBackEdges (n : Node) : CPP Unit := do
  let mut toVisit : Array Node := #[]
  if !(← get).seen.contains ⟨n⟩ then
    toVisit := toVisit.push n
    modify fun s => { s with seen := s.seen.insert ⟨n⟩ }
  modify fun s => { s with backEdges := s.backEdges.alter ⟨n⟩ (·.orElse fun _ => some #[]) }
  let mut i := 0
  while i < toVisit.size do
    let cur := toVisit[i]!
    i := i + 1
    if theoryOf cur == .THEORY_BOOL then
      for c in cur.getChildren do
        modify fun s =>
          let be := s.backEdges
          let s := { s with backEdges := {} }
          { s with backEdges := be.alter ⟨c⟩ fun es => some ((es.getD #[]).push cur) }
        if !(← get).seen.contains ⟨c⟩ then
          toVisit := toVisit.push c
          modify fun s => { s with seen := s.seen.insert ⟨c⟩ }

partial def assertTrue (a : Node) : CPP Unit := do
  match a with
  | .const (.boolean false) => modify fun s => { s with conflict := true }
  | .app (.kind .AND) cs => for c in cs do assertTrue c
  | _ =>
    computeBackEdges a
    assign a true .root

def uniqueHoldout (cs : Array Node) (v : Bool) : CPP (Option Node) := do
  let mut found : Option Node := none
  for c in cs do
    if !(← isAssignedTo c v) then
      if found.isSome then return none
      found := some c
  return found

def propagateBackward (parent : Node) (pv : Bool) : CPP Unit := do
  let cs := parent.getChildren
  let r ← bwdOf parent
  match parent.getKind with
  | .AND =>
    if pv then for c in cs do assign c true r
    else if let some h ← uniqueHoldout cs true then assign h false r
  | .OR =>
    if pv then
      if let some h ← uniqueHoldout cs false then assign h true r
    else for c in cs do assign c false r
  | .NOT =>
    if let some c := cs[0]? then assign c (!pv) r
  | .ITE =>
    let #[c, t, e] := cs | return
    match ← valueOf c with
    | some true => assign t pv r
    | some false => assign e pv r
    | none =>
      match ← valueOf t, ← valueOf e with
      | some vt, some ve =>
        if vt == pv && ve != pv then assign c true r
        else if vt != pv && ve == pv then assign c false r
      | _, _ => pure ()
  | .EQUAL =>
    let #[x, y] := cs | return
    match ← valueOf x, ← valueOf y with
    | some vx, _ => assign y (if pv then vx else !vx) r
    | none, some vy => assign x (if pv then vy else !vy) r
    | none, none => pure ()
  | .IMPLIES =>
    let #[x, y] := cs | return
    if pv then
      if (← valueOf x) == some true then assign y true r
      if (← valueOf y) == some false then assign x false r
    else
      assign x true r
      assign y false r
  | .XOR =>
    let #[x, y] := cs | return
    match ← valueOf x, ← valueOf y with
    | some vx, _ => assign y (if pv then !vx else vx) r
    | none, some vy => assign x (if pv then !vy else vy) r
    | none, none => pure ()
  | _ => pure ()

def propagateForward (child : Node) (cv : Bool) : CPP Unit := do
  let parents := ((← get).backEdges.get? ⟨child⟩).getD #[]
  for parent in parents do
    if (← get).conflict then return
    let cs := parent.getChildren
    match parent.getKind with
    | .AND =>
      if cv then
        if ← cs.allM (isAssignedTo · true) then assign parent true .fwd
        else if ← isAssignedTo parent false then
          if let some h ← uniqueHoldout cs true then assign h false (← bwdOf parent)
      else assign parent false .fwd
    | .OR =>
      if cv then assign parent true .fwd
      else
        if ← cs.allM (isAssignedTo · false) then assign parent false .fwd
        else if ← isAssignedTo parent true then
          if let some h ← uniqueHoldout cs false then assign h true (← bwdOf parent)
    | .NOT => assign parent (!cv) .fwd
    | .ITE =>
      let #[c, t, e] := cs | pure ()
      if child == c then
        if cv then
          if let some vt ← valueOf t then assign parent vt .fwd
        else
          if let some ve ← valueOf e then assign parent ve .fwd
      if child == t then
        if (← valueOf c) == some true then assign parent cv .fwd
      if child == e then
        if (← valueOf c) == some false then assign parent cv .fwd
    | .EQUAL =>
      let #[x, y] := cs | pure ()
      match ← valueOf x, ← valueOf y with
      | some vx, some vy => assign parent (vx == vy) .fwd
      | _, _ =>
        if let some pv ← valueOf parent then
          let r ← bwdOf parent
          if child == x then assign y (if pv then cv else !cv) r
          else assign x (if pv then cv else !cv) r
    | .IMPLIES =>
      let #[x, y] := cs | pure ()
      match ← valueOf x, ← valueOf y with
      | some vx, some vy =>
        if !vx then assign parent true .fwd
        else if vy then assign parent true .fwd
        else assign parent false .fwd
      | _, _ =>
        if let some pv ← valueOf parent then
          let r ← bwdOf parent
          if pv && child == x && cv then assign y true r
          if pv && child == y && !cv then assign x false r
    | .XOR =>
      let #[x, y] := cs | pure ()
      if let some pv ← valueOf parent then
        let r ← bwdOf parent
        if child == x then assign y (cv != pv) r
        else assign x (cv != pv) r
      match ← valueOf x, ← valueOf y with
      | some vx, some vy => assign parent (vx != vy) .fwd
      | _, _ => pure ()
    | _ => pure ()

def propagate : CPP Unit := do
  let mut i := 0
  while i < (← get).queue.size && !(← get).conflict do
    let cur := (← get).queue[i]!
    i := i + 1
    let some v ← valueOf cur | continue
    let isEqOfVars := match cur with
      | .app (.kind .EQUAL) #[a, b] => a.isVar && b.isVar
      | _ => false
    let atom := theoryOf cur != .THEORY_BOOL || cur.isVar || isEqOfVars
    let eqWithVar := match cur with
      | .app (.kind .EQUAL) #[a, b] => a.isVar || b.isVar
      | _ => false
    if atom || eqWithVar then
      let some idx ← indexOf cur | continue
      modify fun s => { s with learned := s.learned.push idx }
    if !atom && !cur.isConst then propagateBackward cur v
    propagateForward cur v

end CPP

/-- The circuit propagator on the assertions `as`: its final state. -/
def runCircuitPure (as : List Node) : CPPState :=
  ((do for a in as do CPP.assertTrue a
       CPP.propagate) : CPP Unit).run {} |>.2

end Telos.Preprocess
