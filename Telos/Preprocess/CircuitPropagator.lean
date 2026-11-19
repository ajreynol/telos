import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Preprocess.ConjProof
import Telos.Rewriter.Rewrite

/-!
# The circuit propagator

A port of cvc5's `CircuitPropagator` (`src/theory/booleans/circuit_propagator.cpp`),
which non-clausal simplification uses to learn literals from the Boolean
structure of the assertions: each assertion is assigned `true`, and assignments
are propagated to children (backward) and to parents (forward) through `and`,
`or`, `not`, `ite`, Boolean `=`, `=>` and `xor`, in the order of a queue. Atoms
(a node of another theory, a variable, an equality of variables) and
equalities with a variable side that get a value are the learned literals.

It runs inside a proof (`Proof.EmitM`) whose assumption is the conjunction of
the assertions, and gives every assignment a fact: `n` for `true`, `(not n)`
for `false`. A fact is derived uniformly from the fact of the node that forced
it: the children of that node that have values are replaced by `true` or
`false` (congruence with `true_intro` and `false_intro`), and the result is
rewritten (for example `(not (and true h true))` to `(not h)`); the cases of all
children are `and_elim` and `not_or_elim`. A failed derivation stops the proof
(the pass then does nothing). A conflict is a fact `false` (`contra`).
-/

namespace Telos.Preprocess

open Eo Node Proof

structure CPState where
  /-- The value of each assigned node, and the position of its fact. -/
  assign : Std.HashMap Key (Bool × Nat) := {}
  queue : Array Node := #[]
  /-- The parents of each node, in the Boolean structure (`d_backEdges`). -/
  backEdges : Std.HashMap Key (Array Node) := {}
  seen : Std.HashSet Key := {}
  /-- The learned literals, with the positions of their facts. -/
  learned : Array (Node × Nat) := #[]
  /-- The position of the fact `false`, after a conflict. -/
  conflict : Option Nat := none

abbrev CPM := StateT CPState EmitM

def CPM.lift {α : Type} (m : EmitM α) : CPM α := fun s => do return (← m, s)

def fail {α : Type} : CPM α := CPM.lift (throw "circuit propagator: no proof")

def valueOf (n : Node) : CPM (Option (Bool × Nat)) := do
  return (← get).assign.get? ⟨n⟩

def isAssignedTo (n : Node) (v : Bool) : CPM Bool := do
  return ((← valueOf n).map (·.1)) == some v

def isAssigned (n : Node) : CPM Bool := do return (← valueOf n).isSome

/-- The literal of `n` with value `v`. -/
def litOf (n : Node) (v : Bool) : Node := if v then n else notNode n

/-- The fact of an assigned node (its literal). -/
def factPos (n : Node) : CPM (Option Nat) := do return (← valueOf n).map (·.2)

/-- Resolve the clause fact at `p` against the facts of children: for `(c, neg)`,
the clause has the literal `(not c)` (`neg`, and `c` is `true`) or `c` (and `c`
is `false`), which resolution with the fact of `c` removes. The result is the
remaining clause, a single literal as itself. -/
def resolveOut (p : Nat) (elims : List (Node × Bool)) : CPM (Option Nat) := do
  let mut p := p
  for (c, neg) in elims do
    let some q ← factPos c | return none
    p ← CPM.lift (stepN .resolution [.term (.Boolean (!neg)), .node c] [p, q])
  return some p

/-- A clause by `rule` on the premise at `p`, then `resolveOut`. -/
def byClause (rule : CRule) (p : Nat) (elims : List (Node × Bool)) : CPM (Option Nat) := do
  resolveOut (← CPM.lift (stepE rule [] [p])) elims

/-- A clause by the premise-free CNF rule `rule` on `P` (with optional index), then `resolveOut`. -/
def byAxiom (rule : CRule) (P : Node) (idx : Option Nat) (elims : List (Node × Bool)) :
    CPM (Option Nat) := do
  let args : List PArg := [.node P] ++ (idx.map fun i => [.term (Term.Numeral (Int.ofNat i))]).getD []
  resolveOut (← CPM.lift (stepN rule args [])) elims

/-- The child `h` of an `and` that is `false` while the others are `true`:
`not_and` on the fact `(not (and …))`, the others resolved away. -/
def andHoldout (parent : Node) (pp : Nat) (h : Node) : CPM (Option Nat) := do
  let others := (parent.getChildren.toList.eraseIdx ((parent.getChildren.toList.idxOf h))).map (·, true)
  byClause .not_and pp others

/-- The child `h` of an `or` that is `true` while the others are `false`: the
fact `(or …)`, the others resolved away. -/
def orHoldout (parent : Node) (pp : Nat) (h : Node) : CPM (Option Nat) := do
  let others := (parent.getChildren.toList.eraseIdx ((parent.getChildren.toList.idxOf h))).map (·, false)
  resolveOut pp others

/-- `makeConflict`: the fact `false` from the facts of `n` and `(not n)`. -/
def conflictOf (pn pnot : Nat) : CPM Unit := do
  if (← get).conflict.isSome then return
  let p ← CPM.lift (stepE .contra [] [pn, pnot])
  modify fun s => { s with conflict := some p }

/-- The fact a derivation gives; none is a failure, unless it found a
conflict instead. -/
def derived (derive : CPM (Option Nat)) : CPM (Option Nat) := do
  match ← derive with
  | some p => return some p
  | none => if (← get).conflict.isSome then return none else fail

/-- `assignAndEnqueue`, with the derivation of the fact of the new literal. -/
def assignE (n : Node) (v : Bool) (derive : CPM (Option Nat)) : CPM Unit := do
  if (← get).conflict.isSome then return
  match n with
  | .const (.boolean b) =>
    if b != v then
      -- the fact `(not true)` or `false`
      let some p ← derived derive | return
      if b then
        let r := rewriteCert (notNode mkTrue)
        let q ← CPM.lift (eqResolveE p (← CPM.lift (rwFact r)))
        modify fun s => { s with conflict := some q }
      else modify fun s => { s with conflict := some p }
      return
  | _ => pure ()
  match ← valueOf n with
  | some (w, q) =>
    if w != v then
      let some p ← derived derive | return
      if v then conflictOf p q else conflictOf q p
  | none =>
    let some p ← derived derive | return
    modify fun s => { s with assign := s.assign.insert ⟨n⟩ (v, p), queue := s.queue.push n }

/-- `computeBackEdges`. -/
def computeBackEdges (n : Node) : CPM Unit := do
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
        modify fun s => { s with backEdges := s.backEdges.alter ⟨c⟩ fun es => some ((es.getD #[]).push cur) }
        if !(← get).seen.contains ⟨c⟩ then
          toVisit := toVisit.push c
          modify fun s => { s with seen := s.seen.insert ⟨c⟩ }

/-- `assertTrue`, for the assertion `a` whose fact is at `pos`. -/
partial def assertTrue (a : Node) (pos : Nat) : CPM Unit := do
  match a with
  | .const (.boolean false) => modify fun s => { s with conflict := s.conflict.orElse fun _ => some pos }
  | .app (.kind .AND) cs =>
    for h : i in [0:cs.size] do
      let p ← CPM.lift (stepE .and_elim [.Numeral (Int.ofNat i)] [pos])
      assertTrue cs[i] p
  | _ =>
    computeBackEdges a
    assignE a true (pure (some pos))

/-- The children of `n` not assigned `v`: the unique one, if exactly one. -/
def uniqueHoldout (cs : Array Node) (v : Bool) : CPM (Option Node) := do
  let mut found : Option Node := none
  for c in cs do
    if !(← isAssignedTo c v) then
      if found.isSome then return none
      found := some c
  return found

/-- The fact of `parent` with its value. -/
def factOf (n : Node) : CPM (Option (Node × Nat)) := do
  return (← valueOf n).map fun (v, p) => (litOf n v, p)

/-- The other side of a Boolean equality with value `pv`, from the side `k`
(the first if `first`) with value `vk`: `equiv_elim1` (or (not x) y),
`equiv_elim2` (or x (not y)), `not_equiv_elim1` (or x y), `not_equiv_elim2`
(or (not x) (not y)), with `k` resolved away. -/
def eqOther (pp : Nat) (pv : Bool) (k : Node) (vk first : Bool) : CPM (Option Nat) :=
  let rule := match pv, vk, first with
    | true, true, true => CRule.equiv_elim1
    | true, false, true => .equiv_elim2
    | true, true, false => .equiv_elim2
    | true, false, false => .equiv_elim1
    | false, true, _ => .not_equiv_elim2
    | false, false, _ => .not_equiv_elim1
  byClause rule pp [(k, vk)]

/-- The other side of a `xor` with value `pv`, from the side `k` (the first if
`first`) with value `vk`: `xor_elim1` (or x y), `xor_elim2` (or (not x) (not y)),
`not_xor_elim1` (or x (not y)), `not_xor_elim2` (or (not x) y). -/
def xorSide (pp : Nat) (pv : Bool) (k : Node) (vk first : Bool) : CPM (Option Nat) :=
  let rule := match pv, vk, first with
    | true, true, _ => CRule.xor_elim2
    | true, false, _ => .xor_elim1
    | false, true, true => .not_xor_elim2
    | false, false, true => .not_xor_elim1
    | false, true, false => .not_xor_elim1
    | false, false, false => .not_xor_elim2
  byClause rule pp [(k, vk)]

/-- `propagateBackward`, with a rule per case (the facts of the parent and of
the children that have values). -/
def propagateBackward (parent : Node) (pv : Bool) : CPM Unit := do
  let cs := parent.getChildren
  let some (_, pp) ← valueOf parent | return
  let val (n : Node) : CPM (Option Bool) := do return (← valueOf n).map (·.1)
  match parent.getKind with
  | .AND =>
    if pv then
      for h : i in [0:cs.size] do
        assignE cs[i] true (some <$> CPM.lift (stepE .and_elim [.Numeral (Int.ofNat i)] [pp]))
    else if let some h ← uniqueHoldout cs true then assignE h false (andHoldout parent pp h)
  | .OR =>
    if pv then
      if let some h ← uniqueHoldout cs false then assignE h true (orHoldout parent pp h)
    else
      for h : i in [0:cs.size] do
        assignE cs[i] false (some <$> CPM.lift (stepE .not_or_elim [.Numeral (Int.ofNat i)] [pp]))
  | .NOT =>
    match cs[0]? with
    | some c =>
      assignE c (!pv) (if pv then pure (some pp)
        else some <$> CPM.lift (stepE .not_not_elim [] [pp]))
    | none => pure ()
  | .ITE =>
    let #[c, t, e] := cs | return
    match ← val c with
    | some true =>
      assignE t pv (byClause (if pv then .ite_elim1 else .not_ite_elim1) pp [(c, true)])
    | some false =>
      assignE e pv (byClause (if pv then .ite_elim2 else .not_ite_elim2) pp [(c, false)])
    | none =>
      match ← val t, ← val e with
      | some vt, some ve =>
        if vt == pv && ve != pv then
          -- the else branch is not the parent's value: the condition holds
          assignE c true (byClause (if pv then .ite_elim2 else .not_ite_elim2) pp [(e, !pv)])
        else if vt != pv && ve == pv then
          assignE c false (byClause (if pv then .ite_elim1 else .not_ite_elim1) pp [(t, !pv)])
      | _, _ => pure ()
  | .EQUAL =>
    let #[x, y] := cs | return
    match ← val x, ← val y with
    | some vx, _ => assignE y (if pv then vx else !vx) (eqOther pp pv x vx true)
    | none, some vy => assignE x (if pv then vy else !vy) (eqOther pp pv y vy false)
    | none, none => pure ()
  | .IMPLIES =>
    let #[x, y] := cs | return
    if pv then
      if (← val x) == some true then assignE y true (byClause .implies_elim pp [(x, true)])
      if (← val y) == some false then assignE x false (byClause .implies_elim pp [(y, false)])
    else
      assignE x true (some <$> CPM.lift (stepE .not_implies_elim1 [] [pp]))
      assignE y false (some <$> CPM.lift (stepE .not_implies_elim2 [] [pp]))
  | .XOR =>
    let #[x, y] := cs | return
    match ← val x, ← val y with
    | some vx, _ => assignE y (if pv then !vx else vx) (xorSide pp pv x vx true)
    | none, some vy => assignE x (if pv then !vy else vy) (xorSide pp pv y vy false)
    | none, none => pure ()
  | _ => pure ()

/-- `propagateForward`, from `child` with value `cv` to its parents. -/
def propagateForward (child : Node) (cv : Bool) : CPM Unit := do
  let parents := ((← get).backEdges.get? ⟨child⟩).getD #[]
  let val (n : Node) : CPM (Option Bool) := do return (← valueOf n).map (·.1)
  for parent in parents do
    if (← get).conflict.isSome then return
    let cs := parent.getChildren
    match parent.getKind with
    | .AND =>
      if cv then
        if ← cs.allM (isAssignedTo · true) then
          assignE parent true do
            let ps ← cs.toList.mapM factPos
            if ps.any Option.isNone then return none
            some <$> CPM.lift (stepE .and_intro [] (ps.filterMap id))
        else if ← isAssignedTo parent false then
          if let some h ← uniqueHoldout cs true then
            assignE h false do
              let some (_, pp) ← valueOf parent | return none
              andHoldout parent pp h
      else
        assignE parent false (byAxiom .cnf_and_pos parent (some (cs.toList.idxOf child)) [(child, false)])
    | .OR =>
      if cv then
        assignE parent true (byAxiom .cnf_or_neg parent (some (cs.toList.idxOf child)) [(child, true)])
      else
        if ← cs.allM (isAssignedTo · false) then
          assignE parent false (byAxiom .cnf_or_pos parent none (cs.toList.map (·, false)))
        else if ← isAssignedTo parent true then
          if let some h ← uniqueHoldout cs false then
            assignE h true do
              let some (_, pp) ← valueOf parent | return none
              orHoldout parent pp h
    | .NOT =>
      if cv then
        -- `(not (not c))` from `c`, by rewriting it to `c`
        assignE parent false do
          let some q ← factPos child | return none
          let r := rewriteCert (notNode parent)
          if r.1 != child then return none
          some <$> CPM.lift (eqResolveE q (← CPM.lift (symmOpt (← CPM.lift (rwFact r)))))
      else assignE parent true (factPos child)
    | .ITE =>
      let #[c, t, e] := cs | pure ()
      let viaThen (vt : Bool) := assignE parent vt
        (byAxiom (if vt then .cnf_ite_neg1 else .cnf_ite_pos1) parent none [(c, true), (t, vt)])
      let viaElse (ve : Bool) := assignE parent ve
        (byAxiom (if ve then .cnf_ite_neg2 else .cnf_ite_pos2) parent none [(c, false), (e, ve)])
      if child == c then
        if cv then
          match ← val t with
          | some vt => viaThen vt
          | none => pure ()
        else
          match ← val e with
          | some ve => viaElse ve
          | none => pure ()
      if child == t then
        if (← val c) == some true then viaThen cv
      if child == e then
        if (← val c) == some false then viaElse cv
    | .EQUAL =>
      let #[x, y] := cs | pure ()
      match ← val x, ← val y with
      | some vx, some vy =>
        -- `cnf_equiv_neg2`: (or (= x y) (not x) (not y)); `neg1`: (or (= x y) x y);
        -- `pos1`: (or (not (= x y)) (not x) y); `pos2`: (or (not (= x y)) x (not y))
        let rule := match vx, vy with
          | true, true => CRule.cnf_equiv_neg2
          | false, false => .cnf_equiv_neg1
          | true, false => .cnf_equiv_pos1
          | false, true => .cnf_equiv_pos2
        assignE parent (vx == vy) (byAxiom rule parent none [(x, vx), (y, vy)])
      | _, _ =>
        if let some (pv, pp) ← valueOf parent then
          if child == x then assignE y (if pv then cv else !cv) (eqOther pp pv x cv true)
          else assignE x (if pv then cv else !cv) (eqOther pp pv y cv false)
    | .IMPLIES =>
      let #[x, y] := cs | pure ()
      match ← val x, ← val y with
      | some vx, some vy =>
        if !vx then assignE parent true (byAxiom .cnf_implies_neg1 parent none [(x, false)])
        else if vy then assignE parent true (byAxiom .cnf_implies_neg2 parent none [(y, true)])
        else assignE parent false (byAxiom .cnf_implies_pos parent none [(x, true), (y, false)])
      | _, _ =>
        if let some (pv, pp) ← valueOf parent then
          if pv && child == x && cv then assignE y true (byClause .implies_elim pp [(x, true)])
          if pv && child == y && !cv then assignE x false (byClause .implies_elim pp [(y, false)])
    | .XOR =>
      let #[x, y] := cs | pure ()
      if let some (pv, pp) ← valueOf parent then
        if child == x then assignE y (cv != pv) (xorSide pp pv x cv true)
        else assignE x (cv != pv) (xorSide pp pv y cv false)
      match ← val x, ← val y with
      | some vx, some vy =>
        -- `cnf_xor_neg1`: (or (xor x y) (not x) y); `neg2`: (or (xor x y) x (not y));
        -- `pos1`: (or (not (xor x y)) x y); `pos2`: (or (not (xor x y)) (not x) (not y))
        let rule := match vx, vy with
          | true, false => CRule.cnf_xor_neg1
          | false, true => .cnf_xor_neg2
          | false, false => .cnf_xor_pos1
          | true, true => .cnf_xor_pos2
        assignE parent (vx != vy) (byAxiom rule parent none [(x, vx), (y, vy)])
      | _, _ => pure ()
    | _ => pure ()

/-- `propagate`: the queue, in order; atoms with values are learned. -/
def propagate : CPM Unit := do
  let mut i := 0
  while i < (← get).queue.size && (← get).conflict.isNone do
    let cur := (← get).queue[i]!
    i := i + 1
    let some (v, p) ← valueOf cur | continue
    let isEqOfVars := match cur with
      | .app (.kind .EQUAL) #[a, b] => a.isVar && b.isVar
      | _ => false
    let atom := theoryOf cur != .THEORY_BOOL || cur.isVar || isEqOfVars
    let eqWithVar := match cur with
      | .app (.kind .EQUAL) #[a, b] => a.isVar || b.isVar
      | _ => false
    if atom || eqWithVar then
      modify fun s => { s with learned := s.learned.push (litOf cur v, p) }
    if !atom && !cur.isConst then propagateBackward cur v
    propagateForward cur v

end Telos.Preprocess
