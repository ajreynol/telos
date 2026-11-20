import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Node.Order
import Telos.Solver.Event
import Telos.Solver.Theory.DtState

/-!
# The equality engine

A port of cvc5's `eq::EqualityEngine` (`src/theory/uf/equality_engine.cpp`):
congruence closure over curried applications, with an equality graph whose
edges record why two terms were merged, from which explanations are
reconstructed.

The port follows cvc5 closely, because the events that telos compares with
cvc5's (`Telos/Solver/Event.lean`) depend on its details:
- node ids are given in the order terms are added;
- an application `f(t₁, …, tₙ)` is curried into `n` application nodes, of which
  the last is the term's node;
- the merge queue is processed in order;
- the representative is a non-internal node, then a constant, then the larger
  class's, then the first candidate's;
- triggers fire in the order of the merged class's nodes, each node's newest
  first;
- explanations follow cvc5's breadth-first search of the equality graph, with
  the edges of a node newest first.

What is not ported yet:
- trigger terms (shared terms, `addTriggerTerm`) and the trigger-term sets of
  constants (`constantsAreTriggers`), which matter only for theory combination.
  In a logic with one theory, the only classes with trigger-term sets are those
  of `true` and `false`, and their disequality propagation is inert;
- interpreted function kinds and their evaluation (`MERGED_THROUGH_CONSTANTS` of
  `f(c₁, …, cₙ) = c`), which no theory telos has uses yet;
- the master equality engine of quantified logics.

The engine is context dependent, as cvc5's is on the SAT context: `push` saves
its counters (cvc5's `CDO`s: the numbers of nodes, merges, lookups, triggers
and deduced disequalities), and `popTo` restores them and undoes what came
after (`backtrack`, `undoMerge`), in cvc5's order.

Instead of calling back the theory engine (`EqualityEngineNotify`), the engine
records notes (`Note`), which the caller turns into events. The one callback
whose answer matters, the propagation of a trigger predicate, is answered as
cvc5's theory engine answers it on inputs without SAT structure: the
propagation fails exactly when the literal is false in the SAT assignment, or
the engine is already in conflict (`notifyTriggerPredicate`).
-/

namespace Telos.Solver.EE

/-- The kind of an application node (`FunctionApplicationType`). -/
inductive AppType where
  | equality
  | uninterpreted
  | interpreted
  deriving DecidableEq, Hashable, Inhabited, Repr

/-- `FunctionApplication`: the application of `a` to `b`, or the equality of `a`
and `b`. -/
structure FunApp where
  type : AppType
  a : Nat
  b : Nat
  deriving DecidableEq, Hashable, Inhabited, Repr

instance : BEq FunApp := ⟨fun x y => decide (x = y)⟩

/-- Why two nodes were merged (`MergeReasonType`). -/
inductive MergeReason where
  | congruence
  | equality
  | reflexivity
  | constants
  deriving DecidableEq, Inhabited, Repr

/-- A pending merge (`MergeCandidate`). -/
structure Candidate where
  t1 : Nat
  t2 : Nat
  type : MergeReason
  reason : Node
  deriving Inhabited

/-- A node of the union-find structure (`EqualityNode`): its representative,
the next node of its class (a ring), the size of its class (meaningful at the
representative), and the head of its use list. -/
structure ENode where
  find : Nat
  next : Nat
  size : Nat := 1
  useList : Option Nat := none
  deriving Inhabited

structure UseNode where
  app : Nat
  next : Option Nat
  deriving Inhabited

/-- An edge of the equality graph. Edges come in pairs `2k`, `2k+1`, one for
each direction. -/
structure Edge where
  node : Nat
  next : Option Nat
  type : MergeReason
  reason : Node
  deriving Inhabited

/-- One half of a trigger: the class of its side, and the next trigger of the
same node. Triggers come in pairs `2k`, `2k+1`, one for each side. -/
structure Trigger where
  classId : Nat
  next : Option Nat
  deriving Inhabited

structure TriggerInfo where
  trigger : Node
  polarity : Bool
  deriving Inhabited

/-- What the engine tells its owner, in order (`EqualityEngineNotify`). -/
inductive Note where
  | newClass (t : Node)
  | merge (t₁ t₂ : Node)
  | disequal (t₁ t₂ reason : Node)
  /-- A trigger predicate became true (`lit`) or false (`(not lit)`). -/
  | propagate (lit : Node)
  /-- Two constants were merged: the engine is inconsistent. -/
  | constantMerge (t₁ t₂ : Node)
  /-- A theory's output, from a notification or a check: an internal fact (with
  its explanation), a lemma, a conflict (as its explanation). -/
  | fact (T : Theory) (id : String) (lit exp : Node)
  | lemma (T : Theory) (id : String) (lem : Node)
  | conflict (T : Theory) (id : String) (exp : Node)
  /-- A shared equality (or disequality) for the theory with tag `tag`
  (`SharedSolver::propagateSharedEquality`), after its propagation. -/
  | sharedEq (tag : Nat) (lit : Node)
  deriving Inhabited

/-- The context-dependent counters of the engine, saved at each push. -/
structure Counters where
  nodes : Nat
  assertedEqs : Nat
  lookups : Nat
  triggers : Nat
  deducedDiseqs : Nat
  deducedReasons : Nat
  propLog : Nat
  tsetLog : Nat
  done : Bool
  deriving Inhabited

/-- A set of trigger terms (`TriggerTermSet`): for each tag (a theory, by cvc5's
`TheoryId`), the trigger term of the class, sorted by tag. -/
abbrev TSet := Array (Nat × Nat)

/-- The number of cvc5's theories (`THEORY_LAST`), all of which are tags of the
trigger sets of constants. -/
def numTags : Nat := 14

/-- The tag of a theory: its `TheoryId` in cvc5. -/
def _root_.Telos.Solver.Theory.tag : Theory → Nat
  | .THEORY_BUILTIN => 0
  | .THEORY_BOOL => 1
  | .THEORY_UF => 2
  | .THEORY_ARITH => 3
  | .THEORY_BV => 4
  | .THEORY_ARRAYS => 7
  | .THEORY_DATATYPES => 8
  | .THEORY_SETS => 10
  | .THEORY_STRINGS => 12
  | .THEORY_QUANTIFIERS => 13

/-- The tags of a trigger set, as a bit set. -/
def TSet.tags (t : Option TSet) : Nat :=
  match t with
  | some ts => ts.foldl (fun m (tag, _) => m ||| (1 <<< tag)) 0
  | none => 0

def TSet.get (ts : TSet) (tag : Nat) : Nat := ((ts.find? (·.1 == tag)).map (·.2)).getD 0

/-- The tags of a bit set, in increasing order. -/
def tagList (m : Nat) : List Nat := (List.range numTags).filter fun t => (m >>> t) % 2 == 1

/-- The tag of `THEORY_LAST`, which cvc5 uses to mark a disequality as
propagated with its reasons stored. -/
def lastTag : Nat := 63

structure EqualityEngine where
  nodes : Array Node := #[]
  nodeIds : Std.HashMap Key Nat := {}
  /-- The original and normalized application of each application node. -/
  apps : Array (Option (FunApp × FunApp)) := #[]
  enodes : Array ENode := #[]
  useNodes : Array UseNode := #[]
  /-- The newest edge of each node. -/
  graph : Array (Option Nat) := #[]
  edges : Array Edge := #[]
  /-- The newest trigger of each node. -/
  nodeTriggers : Array (Option Nat) := #[]
  triggers : Array Trigger := #[]
  triggerInfos : Array TriggerInfo := #[]
  isConstant : Array Bool := #[]
  isInternal : Array Bool := #[]
  isEquality : Array Bool := #[]
  lookup : Std.HashMap FunApp Nat := {}
  queue : Array Candidate := #[]
  qhead : Nat := 0
  inPropagate : Bool := false
  /-- The engine is inconsistent (`d_done`): it ignores further work. -/
  done : Bool := false
  /-- The disequalities propagated, with the tags they were propagated for. -/
  propagatedDiseqs : Std.HashMap (Nat × Nat) Nat := {}
  /-- The reasons of each propagated disequality: a range of `deducedReasons`. -/
  diseqReasons : Std.HashMap (Nat × Nat) (Nat × Nat) := {}
  deducedReasons : Array (Nat × Nat) := #[]
  deducedReasonsSize : Nat := 0
  trueId : Nat := 0
  falseId : Nat := 1
  notes : Array Note := #[]
  /-- The theory engine is in conflict: a propagation failed. -/
  teConflict : Bool := false
  /-- The merges, in order (`d_assertedEqualities`): the class kept and the
  class merged into it, or `none` for a merge of constants. -/
  assertedEqs : Array (Option (Nat × Nat)) := #[]
  /-- The lookups stored, in order (`d_applicationLookups`). -/
  appLookups : Array FunApp := #[]
  /-- The disequalities whose reasons were stored, in order
  (`d_deducedDisequalities`). -/
  deducedDiseqs : Array (Nat × Nat) := #[]
  /-- The previous values of the entries of `propagatedDiseqs` set, in order
  (it is a `CDHashMap` in cvc5). -/
  propLog : Array ((Nat × Nat) × Option Nat) := #[]
  /-- The counters saved at each push: the `i`-th, when leaving level `i`. -/
  saved : Array Counters := #[]
  /-- The trigger terms of each class (`d_nodeIndividualTrigger`). -/
  termTriggers : Array (Option TSet) := #[]
  /-- The updates of `termTriggers`, with the previous values, in order
  (`d_triggerTermSetUpdates`). -/
  tsetLog : Array (Nat × Option TSet) := #[]
  /-- The state of the theory of datatypes, which reacts to the engine's
  notifications (`Telos/Solver/Theory/Datatypes.lean`). -/
  dt : DT.State := {}
  deriving Inhabited

/-- What the engine reads from its owner. -/
structure Ctx where
  /-- The kinds whose applications are congruence-closed (`addFunctionKind`). -/
  congruenceKinds : Kind → Bool
  /-- The SAT value of an atom. -/
  value : Node → Option Bool
  /-- The theories' handling of a notification (`.newClass`, `.merge`), called
  when it happens, as cvc5's `EqualityEngineNotify` is: it reads the engine as it
  is then, and records its outputs as notes. -/
  onNote : Note → EqualityEngine → EqualityEngine := fun _ ee => ee

abbrev EEM := ReaderT Ctx (StateM EqualityEngine)

/-- A constant, in cvc5's sense (`Node::isConst`). -/
def isConstNode (n : Node) : Bool := n.isConst

def note (n : Note) : EEM Unit := modify fun s => { s with notes := s.notes.push n }

/-- Record a notification and let the theories handle it now. -/
def notify (n : Note) : EEM Unit := do
  note n
  let f := (← read).onNote
  modify (f n)

/-- Update the state of the theory of datatypes in place. -/
def modifyDt (f : DT.State → DT.State) : EEM Unit := do
  let dt ← modifyGet fun s => (s.dt, { s with dt := {} })
  modify fun s => { s with dt := f dt }

def find (ee : EqualityEngine) (id : Nat) : Nat := ee.enodes[id]!.find

def getFind (id : Nat) : EEM Nat := do return find (← get) id

def hasTerm (t : Node) : EEM Bool := do return (← get).nodeIds.contains ⟨t⟩

def nodeId (t : Node) : EEM Nat := do return (← get).nodeIds.getD ⟨t⟩ 0

def enqueue (c : Candidate) : EEM Unit := modify fun s => { s with queue := s.queue.push c }

/-- `newNode`: a fresh node for `t`, its own class. -/
def newNode (t : Node) : EEM Nat :=
  modifyGet fun s =>
    let id := s.nodes.size
    (id, { s with
      nodes := s.nodes.push t
      nodeIds := s.nodeIds.insert ⟨t⟩ id
      apps := s.apps.push none
      enodes := s.enodes.push { find := id, next := id }
      graph := s.graph.push none
      nodeTriggers := s.nodeTriggers.push none
      termTriggers := s.termTriggers.push none
      isConstant := s.isConstant.push false
      isInternal := s.isInternal.push true
      isEquality := s.isEquality.push false })

/-- `storeApplicationLookup`: `funId` is the application of its normalized
form; an equality of a class with itself is true, of two constants false. -/
def storeApplicationLookup (norm : FunApp) (funId : Nat) : EEM Unit := do
  modify fun s => { s with lookup := s.lookup.insert norm funId,
                           appLookups := s.appLookups.push norm }
  if norm.type == .equality then
    let s ← get
    if norm.a == norm.b then
      enqueue { t1 := funId, t2 := s.trueId, type := .reflexivity, reason := Node.mkTrue }
    else if s.isConstant[norm.a]! && s.isConstant[norm.b]! then
      enqueue { t1 := funId, t2 := s.falseId, type := .constants, reason := Node.mkTrue }

/-- `usedIn`: `funId` uses the node `id`. -/
def usedIn (id funId : Nat) : EEM Unit :=
  modify fun s =>
    let u := s.useNodes.size
    let old := s.enodes[id]!.useList
    { s with useNodes := s.useNodes.push { app := funId, next := old }
             enodes := s.enodes.modify id fun n => { n with useList := some u } }

/-- `newApplicationNode`: the application of `t₁` to `t₂` (or their equality),
for the term `original`; merged by congruence with an existing application of
the same classes. -/
def newApplicationNode (original : Node) (t₁ t₂ : Nat) (type : AppType) : EEM Nat := do
  let funId ← newNode original
  let s ← get
  let orig : FunApp := { type, a := t₁, b := t₂ }
  let norm : FunApp := { type, a := find s t₁, b := find s t₂ }
  let existing := s.lookup.get? norm
  modify fun s => { s with apps := s.apps.set! funId (some (orig, norm)) }
  match existing with
  | none => storeApplicationLookup norm funId
  | some other => enqueue { t1 := funId, t2 := other, type := .congruence, reason := Node.mkTrue }
  usedIn t₁ funId
  usedIn t₂ funId
  return funId

/-- `addGraphEdge`. -/
def addGraphEdge (t₁ t₂ : Nat) (type : MergeReason) (reason : Node) : EEM Unit :=
  modify fun s =>
    let e := s.edges.size
    let g1 := s.graph[t₁]!
    let g2 := s.graph[t₂]!
    { s with
      edges := (s.edges.push { node := t₂, next := g1, type, reason }).push
        { node := t₁, next := g2, type, reason }
      graph := (s.graph.set! t₁ (some e)).set! t₂ (some (e + 1)) }

def hasPropagatedDiseq (l r : Nat) : EEM Bool := do
  return (← get).propagatedDiseqs.contains (l, r)

def hasPropagatedDiseqTag (tag l r : Nat) : EEM Bool := do
  return match (← get).propagatedDiseqs.get? (l, r) with
    | some tags => (tags >>> tag) % 2 == 1
    | none => false

/-- `storePropagatedDisequality`: with the reasons pushed since the last one,
if any. -/
def storePropagatedDiseq (tag l r : Nat) : EEM Unit := do
  -- take the maps and the log out of the state, so that they are updated in place
  let (pd, log) ← modifyGet fun s => ((s.propagatedDiseqs, s.propLog), { s with propagatedDiseqs := {}, propLog := #[] })
  let tags := (pd.getD (l, r) 0) ||| (1 <<< tag)
  let log := (log.push ((l, r), pd.get? (l, r))).push ((r, l), pd.get? (r, l))
  let pd := (pd.insert (l, r) tags).insert (r, l) tags
  modify fun s =>
    if s.deducedReasons.size > s.deducedReasonsSize then
      let ref := (s.deducedReasonsSize, s.deducedReasons.size)
      { s with propagatedDiseqs := pd, propLog := log
               diseqReasons := (s.diseqReasons.insert (l, r) ref).insert (r, l) ref
               deducedDiseqs := s.deducedDiseqs.push (l, r)
               deducedReasonsSize := s.deducedReasons.size }
    else { s with propagatedDiseqs := pd, propLog := log }

def pushReason (a b : Nat) : EEM Unit :=
  modify fun s => { s with deducedReasons := s.deducedReasons.push (a, b) }

/-- The notification of a trigger predicate, answered as cvc5's theory engine
does without sharing (`TheoryEngine::propagate`): it fails if the engine is in
conflict, or the literal is false in the SAT assignment, which puts the engine
in conflict. -/
def notifyTriggerPredicate (p : Node) (value : Bool) : EEM Bool := do
  let lit := if value then p else Node.notNode p
  -- in a conflict, nothing is propagated (`TheoryInferenceManager::propagateLit`)
  if (← get).teConflict then return false
  note (.propagate lit)
  match (← read).value p with
  | some v =>
    if v != value then
      modify fun s => { s with teConflict := true }
      return false
    return true
  | none => return true

/-! ### Trigger terms -/

/-- Set the trigger set of a class, logging the previous one. -/
def setTermTriggers (c : Nat) (v : Option TSet) : EEM Unit := do
  let (tt, log) ← modifyGet fun s => ((s.termTriggers, s.tsetLog), { s with termTriggers := #[], tsetLog := #[] })
  let log := log.push (c, tt[c]!)
  modify fun s => { s with termTriggers := tt.set! c v, tsetLog := log }

/-- `notifyTriggerTermEquality`, answered as cvc5's central equality engine
manager does (`eqNotifyTriggerTermEquality`): the (dis)equality, oriented by
the order of nodes, is propagated, and given to the theory of the tag as a
shared equality (unless it is UF). -/
def notifyTriggerTermEquality (tag : Nat) (t₁ t₂ : Node) (value : Bool) : EEM Bool := do
  let (a, b) := if Node.lt t₂ t₁ then (t₂, t₁) else (t₁, t₂)
  let eq := Node.eqNode a b
  let lit := if value then eq else Node.notNode eq
  if (← get).teConflict then return false
  note (.propagate lit)
  if let some v := (← read).value eq then
    if v != value then
      modify fun s => { s with teConflict := true }
      return false
  if tag != Theory.THEORY_UF.tag then note (.sharedEq tag lit)
  return true

/-- A disequality of a class, to be propagated for tags (`TaggedEquality`):
the equality, the trigger set of the other side's class, and whether the class
is its left side. -/
structure TaggedEq where
  eqId : Nat
  tset : TSet
  lhs : Bool

/-- `getDisequalities`: the equalities asserted false with a side in the class
`c`, whose other side's class has triggers for some of `tags`. -/
def getDisequalities (allowConstants : Bool) (c : Nat) (tags : Nat) : EEM (Array TaggedEq) := do
  if tags == 0 then return #[]
  let mut out : Array TaggedEq := #[]
  let mut visited : Std.HashSet Nat := {}
  let mut cur := c
  let mut fuel := (← get).enodes.size + 1
  repeat
    if fuel == 0 then break
    fuel := fuel - 1
    let s ← get
    let mut u := s.enodes[cur]!.useList
    while h : u.isSome do
      let uid := u.get h
      let use := s.useNodes[uid]!
      let funId := use.app
      let fn := (s.apps[funId]!.map (·.1)).getD default
      if fn.type == .equality && find s funId == find s s.falseId then
        let (toCompare, lhs) := if fn.b == cur then (fn.a, true) else (fn.b, false)
        let rep := find s toCompare
        if rep == c then return #[]
        if !visited.contains rep then
          visited := visited.insert rep
          if allowConstants || !s.isConstant[rep]! then
            if let some ts := s.termTriggers[rep]! then
              if TSet.tags (some ts) &&& tags != 0 then
                out := out.push { eqId := funId, tset := ts, lhs }
      u := use.next
    cur := s.enodes[cur]!.next
    if s.done || cur == c then break
  return out

/-- `propagateTriggerTermDisequalities`: the disequalities of a class whose
trigger set is `ts`, for the tags `tags`. -/
def propagateTriggerTermDiseqs (tags : Nat) (ts : Option TSet) (diseqs : Array TaggedEq) :
    EEM Bool := do
  if tags == 0 then return !(← get).done
  let some my := ts | return !(← get).done
  for d in diseqs do
    if (← get).done then break
    let common := TSet.tags (some d.tset) &&& tags
    let s ← get
    let fn := (s.apps[d.eqId]!.map (·.1)).getD default
    let (toCompare, myCompare) := if d.lhs then (fn.a, fn.b) else (fn.b, fn.a)
    if find s toCompare == find s myCompare then return !(← get).done
    for tag in tagList common do
      if (← get).done then break
      let tagRep := d.tset.get tag
      let myRep := my.get tag
      if !(← hasPropagatedDiseqTag tag myRep tagRep) then
        if !(← hasPropagatedDiseq myRep tagRep) then
          pushReason myCompare myRep
          pushReason toCompare tagRep
          pushReason d.eqId (← get).falseId
        storePropagatedDiseq tag myRep tagRep
        let s ← get
        if !(← notifyTriggerTermEquality tag s.nodes[myRep]! s.nodes[tagRep]! false) then
          modify fun s => { s with done := true }
  return !(← get).done

/-- `merge`: the class `c₂` into the class `c₁`. Returns the triggers fired. -/
def merge (c₁ c₂ : Nat) : EEM (Array Nat × Bool) := do
  let s ← get
  let n₁ := s.nodes[c₁]!
  let n₂ := s.nodes[c₂]!
  -- the trigger terms of the classes, and their disequalities to propagate
  let ts₁ := s.termTriggers[c₁]!
  let ts₂ := s.termTriggers[c₂]!
  let tags₁ := TSet.tags ts₁
  let tags₂ := TSet.tags ts₂
  let only₁ := tags₁ ^^^ (tags₁ &&& tags₂)
  let only₂ := tags₂ ^^^ (tags₁ &&& tags₂)
  let const₁ := s.isConstant[c₁]!
  let const₂ := s.isConstant[c₂]!
  let (diseqs₂, diseqs₁) ← if !const₁ || !const₂ then do
      let d₂ ← getDisequalities (!const₁) c₂ only₁
      let d₁ ← getDisequalities (!const₂) c₁ only₂
      pure (d₂, d₁)
    else pure (#[], #[])
  let doNotify := find s (s.nodeIds.getD ⟨n₁⟩ 0) == c₁ && find s (s.nodeIds.getD ⟨n₂⟩ 0) == c₂
  -- update the representative of the nodes of class 2, and fire triggers
  let mut fired : Array Nat := #[]
  let mut cur := c₂
  repeat
    modify fun s => { s with enodes := s.enodes.modify cur fun n => { n with find := c₁ } }
    let mut t := (← get).nodeTriggers[cur]!
    while h : t.isSome do
      let tid := t.get h
      let s ← get
      let trig := s.triggers[tid]!
      let other := s.triggers[tid ^^^ 1]!
      if other.classId != trig.classId then
        modify fun s => { s with triggers := s.triggers.modify tid fun x => { x with classId := c₁ } }
        if other.classId == c₁ then fired := fired.push tid
      t := trig.next
    cur := (← get).enodes[cur]!.next
    if cur == c₂ then break
  -- update the lookups of the applications using class 2
  if !(← get).isEquality[c₂]! then
    repeat
      let mut u := (← get).enodes[cur]!.useList
      while h : u.isSome do
        let uid := u.get h
        let s ← get
        let use := s.useNodes[uid]!
        let funId := use.app
        let fn := (s.apps[funId]!.map (·.2)).getD default
        let norm : FunApp := { type := fn.type, a := find s fn.a, b := find s fn.b }
        match s.lookup.get? norm with
        | some other =>
          if find s funId != find s other then
            enqueue { t1 := funId, t2 := other, type := .congruence, reason := Node.mkTrue }
        | none => storeApplicationLookup norm funId
        u := use.next
      cur := (← get).enodes[cur]!.next
      if cur == c₂ then break
  -- merge the rings
  modify fun s =>
    let e₁ := s.enodes[c₁]!
    let e₂ := s.enodes[c₂]!
    let e₁' : ENode := { e₁ with next := e₂.next, size := e₁.size + e₂.size }
    let e₂' : ENode := { e₂ with next := e₁.next }
    { s with enodes := (s.enodes.set! c₁ e₁').set! c₂ e₂' }
  if doNotify then notify (.merge n₁ n₂)
  -- the disequalities of the trigger terms
  if !(← propagateTriggerTermDiseqs only₁ ts₁ diseqs₂) then return (fired, false)
  if !(← propagateTriggerTermDiseqs only₂ ts₂ diseqs₁) then return (fired, false)
  -- the trigger terms of both classes, with a notification for each common tag
  if let some s₂ := ts₂ then
    match ts₁ with
    | none => setTermTriggers c₁ (some s₂)
    | some s₁ =>
      let mut merged : TSet := #[]
      for tag in tagList (tags₁ ||| tags₂) do
        let in₁ := (tags₁ >>> tag) % 2 == 1
        let in₂ := (tags₂ >>> tag) % 2 == 1
        if in₁ then
          merged := merged.push (tag, s₁.get tag)
          if in₂ then
            let s ← get
            if !(← notifyTriggerTermEquality tag s.nodes[s₁.get tag]! s.nodes[s₂.get tag]! true) then
              return (fired, false)
        else merged := merged.push (tag, s₂.get tag)
      if tags₁ != tags₂ then setTermTriggers c₁ (some merged)
  return (fired, true)

/-- `propagate`: process the merge queue. -/
def propagate : EEM Unit := do
  if (← get).inPropagate then return
  modify fun s => { s with inPropagate := true }
  repeat
    let s ← get
    if s.qhead ≥ s.queue.size then break
    if s.done then
      modify fun s => { s with queue := #[], qhead := 0 }
      continue
    let cand := s.queue[s.qhead]!
    modify fun s => { s with qhead := s.qhead + 1 }
    let s ← get
    let c₁ := find s cand.t1
    let c₂ := find s cand.t2
    if c₁ == c₂ then continue
    addGraphEdge cand.t1 cand.t2 cand.type cand.reason
    let s ← get
    if s.isConstant[c₁]! && s.isConstant[c₂]! then
      modify fun s => { s with done := true, teConflict := true,
                               assertedEqs := s.assertedEqs.push none }
      note (.constantMerge s.nodes[c₁]! s.nodes[c₂]!)
      continue
    let into :=
      if s.isInternal[c₂]! != s.isInternal[c₁]! then
        if s.isInternal[c₁]! then c₂ else c₁
      else if s.isConstant[c₂]! != s.isConstant[c₁]! then
        if s.isConstant[c₂]! then c₂ else c₁
      else if s.enodes[c₂]!.size > s.enodes[c₁]!.size then c₂
      else c₁
    let other := if into == c₂ then c₁ else c₂
    modify fun s => { s with assertedEqs := s.assertedEqs.push (some (into, other)) }
    let (fired, ok) ← merge into other
    if !ok then modify fun s => { s with done := true }
    for tid in fired do
      if (← get).done then break
      let info := (← get).triggerInfos[tid]!
      let ok ← match info.trigger with
        | .app (.kind .EQUAL) #[lhs, rhs] =>
          if !info.polarity then do
            let original ← nodeId info.trigger
            let l ← nodeId lhs
            let r ← nodeId rhs
            if !(← hasPropagatedDiseqTag lastTag l r) then
              if !(← hasPropagatedDiseq l r) then pushReason original (← get).falseId
              storePropagatedDiseq lastTag l r
              notifyTriggerPredicate info.trigger info.polarity
            else pure true
          else notifyTriggerPredicate info.trigger info.polarity
        | _ => notifyTriggerPredicate info.trigger info.polarity
      if !ok then modify fun s => { s with done := true }
  modify fun s => { s with inPropagate := false, queue := #[], qhead := 0 }

/-- The node of the operator `f` of an application of kind `k`. A tester's is
not its constructor's: in cvc5 they are different nodes (`is_C` and `C`), and
the tester of `x` must not be the partial application of `C` to `x`. -/
def operatorNode (k : Kind) (f : Node) : Node :=
  if k == .APPLY_TESTER then .app (.kind .APPLY_TESTER) #[f] else f

/-- The operator node and the arguments of a congruence application, if `t` is
one. -/
def congruenceApp (t : Node) : EEM (Option (Node × Array Node)) := do
  match t with
  | .app (.node k f) cs =>
    if (← read).congruenceKinds k && cs.size > 0 then return some (operatorNode k f, cs)
    else return none
  | _ => return none

/-- `addTermInternal`. -/
partial def addTermInternal (t : Node) (isOperator : Bool := false) : EEM Unit := do
  if (← hasTerm t) || (← get).done then return
  let result ← match t with
    | .app (.kind .EQUAL) #[l, r] => do
      addTermInternal l
      addTermInternal r
      let res ← newApplicationNode t (← nodeId l) (← nodeId r) .equality
      modify fun s => { s with isInternal := s.isInternal.set! res false,
                               isConstant := s.isConstant.set! res false }
      pure res
    | _ => do
      match ← congruenceApp t with
      | some (op, cs) =>
        -- APPLY_UF is not an external operator kind: its operator is internal
        addTermInternal op true
        let mut res ← nodeId op
        for c in cs do
          addTermInternal c
          res ← newApplicationNode t res (← nodeId c) .uninterpreted
        let res' := res
        modify fun s => { s with isInternal := s.isInternal.set! res' false,
                                 isConstant := s.isConstant.set! res' (isConstNode t) }
        pure res
      | none => do
        let res ← newNode t
        modify fun s => { s with isInternal := s.isInternal.set! res isOperator,
                                 isConstant := s.isConstant.set! res (!isOperator && isConstNode t) }
        pure res
  match t with
  | .app (.kind .EQUAL) _ => modify fun s => { s with isEquality := s.isEquality.set! result true }
  | _ =>
    notify (.newClass t)
    -- constants are trigger terms for every tag (`d_constantsAreTriggers`)
    if (← get).isConstant[result]! then
      setTermTriggers result (some ((Array.range numTags).map (·, result)))
  propagate

/-- `addTerm`. -/
def addTerm (t : Node) : EEM Unit := addTermInternal t

/-- The initial engine, with `true` and `false` (`init`). Their classes are not
notified, as in cvc5, whose notification class is set after `init`. -/
def init (c : Ctx) : EqualityEngine :=
  let ((), s) := ((do addTerm Node.mkTrue; addTerm Node.mkFalse : EEM Unit).run c).run {}
  { s with trueId := s.nodeIds.getD ⟨Node.mkTrue⟩ 0, falseId := s.nodeIds.getD ⟨Node.mkFalse⟩ 1,
           notes := #[] }

def areEqual (t₁ t₂ : Node) : EEM Bool := do
  let s ← get
  return find s (s.nodeIds.getD ⟨t₁⟩ 0) == find s (s.nodeIds.getD ⟨t₂⟩ 0)

/-- `areDisequal`: with `ensureProof`, the reasons of a deduced disequality are
stored, for its explanation. -/
def areDisequal (t₁ t₂ : Node) (ensureProof : Bool) : EEM Bool := do
  let i₁ ← nodeId t₁
  let i₂ ← nodeId t₂
  if ← hasPropagatedDiseq i₁ i₂ then return true
  let s ← get
  let c₁ := find s i₁
  let c₂ := find s i₂
  if s.isConstant[c₁]! && s.isConstant[c₂]! && c₁ != c₂ then
    if ensureProof then
      pushReason i₁ c₁
      pushReason i₂ c₂
      storePropagatedDiseq lastTag i₁ i₂
    return true
  let falseClass := find s s.falseId
  let check (a b : Nat) (x y : Nat) : EEM Bool := do
    let s ← get
    match s.lookup.get? { type := .equality, a, b } with
    | some e =>
      if find s e == falseClass then
        if ensureProof then
          let orig := (s.apps[e]!.map (·.1)).getD default
          pushReason x orig.a
          pushReason e s.falseId
          pushReason y orig.b
          storePropagatedDiseq lastTag i₁ i₂
        return true
      return false
    | none => return false
  if ← check c₁ c₂ i₁ i₂ then return true
  check c₂ c₁ i₂ i₁

/-- `addTriggerEqualityInternal`. -/
def addTriggerEqualityInternal (t₁ t₂ trigger : Node) (polarity : Bool) : EEM Unit := do
  if (← get).done then return
  let s ← get
  let c₁ := find s (s.nodeIds.getD ⟨t₁⟩ 0)
  let c₂ := find s (s.nodeIds.getD ⟨t₂⟩ 0)
  modify fun s =>
    let id := s.triggers.size
    let p₁ := s.nodeTriggers[c₁]!
    let s := { s with triggers := s.triggers.push { classId := c₁, next := p₁ },
                      triggerInfos := s.triggerInfos.push { trigger, polarity } }
    let p₂ := s.nodeTriggers[c₂]!
    { s with triggers := s.triggers.push { classId := c₂, next := p₂ },
             triggerInfos := s.triggerInfos.push { trigger, polarity },
             nodeTriggers := (s.nodeTriggers.set! c₁ (some id)).set! c₂ (some (id + 1)) }

/-- `addTriggerEquality`. -/
def addTriggerEquality (eq : Node) : EEM Unit := do
  let .app (.kind .EQUAL) #[l, r] := eq | return
  if (← get).done then return
  addTermInternal l
  addTermInternal r
  let mut skip := false
  if ← areEqual l r then
    let _ ← notifyTriggerPredicate eq true
    skip := true
  if ← areDisequal l r true then
    let _ ← notifyTriggerPredicate eq false
    skip := true
  if skip then return
  addTermInternal eq
  addTriggerEqualityInternal l r eq true
  addTriggerEqualityInternal eq Node.mkFalse eq false

/-- `addTriggerPredicate`. -/
def addTriggerPredicate (p : Node) : EEM Unit := do
  if let .app (.kind .EQUAL) _ := p then return ← addTriggerEquality p
  if (← get).done then return
  addTermInternal p
  let mut skip := false
  if ← areEqual p Node.mkTrue then
    let _ ← notifyTriggerPredicate p true
    skip := true
  if ← areEqual p Node.mkFalse then
    let _ ← notifyTriggerPredicate p false
    skip := true
  if skip then return
  addTriggerEqualityInternal p Node.mkTrue p true
  addTriggerEqualityInternal p Node.mkFalse p false

/-- `assertEqualityInternal`. -/
def assertEqualityInternal (t₁ t₂ reason : Node) : EEM Unit := do
  if (← get).done then return
  addTermInternal t₁
  addTermInternal t₂
  enqueue { t1 := ← nodeId t₁, t2 := ← nodeId t₂, type := .equality, reason }

/-- `assertPredicate`. -/
def assertPredicate (t : Node) (polarity : Bool) (reason : Node) : EEM Bool := do
  let b := Node.mkBool polarity
  if (← hasTerm t) && (← areEqual t b) then return false
  assertEqualityInternal t b reason
  propagate
  return true

/-- `assertEquality`. The disequality propagation of trigger terms is not
ported (see the module documentation). -/
def assertEquality (eq : Node) (polarity : Bool) (reason : Node) : EEM Bool := do
  let .app (.kind .EQUAL) #[l, r] := eq | return false
  if polarity then
    if (← hasTerm l) && (← hasTerm r) && (← areEqual l r) then return false
    assertEqualityInternal l r reason
    propagate
  else
    if (← hasTerm l) && (← hasTerm r) && (← areDisequal l r false) then return false
    note (.disequal l r reason)
    assertEqualityInternal eq Node.mkFalse reason
    propagate
    if (← get).done then return true
    -- the disequality of the trigger terms of the two classes, for each common tag
    let a ← nodeId l
    let b ← nodeId r
    let eqId ← nodeId eq
    let s ← get
    let ca := find s a
    let cb := find s b
    if s.isConstant[ca]! && s.isConstant[cb]! then return true
    if let (some ta, some tb) := (s.termTriggers[ca]!, s.termTriggers[cb]!) then
      for tag in tagList (TSet.tags (some ta) &&& TSet.tags (some tb)) do
        let aShared := ta.get tag
        let bShared := tb.get tag
        if !(← hasPropagatedDiseqTag tag aShared bShared) then
          if !(← hasPropagatedDiseq aShared bShared) then
            pushReason aShared a
            pushReason bShared b
            pushReason eqId (← get).falseId
          storePropagatedDiseq tag aShared bShared
          let s ← get
          if !(← notifyTriggerTermEquality tag s.nodes[aShared]! s.nodes[bShared]! false) then break
  return true

/-- `addTriggerTerm`: `t` is a trigger term of the theory with tag `tag`. -/
def addTriggerTerm (t : Node) (tag : Nat) : EEM Unit := do
  if (← get).done then return
  addTermInternal t
  let id ← nodeId t
  let s ← get
  let c := find s id
  let ts := s.termTriggers[c]!
  if (TSet.tags ts >>> tag) % 2 == 1 then
    let trig := (ts.getD #[]).get tag
    if id != trig then
      if !(← notifyTriggerTermEquality tag t s.nodes[trig]! true) then
        modify fun s => { s with done := true }
  else
    let diseqs ← getDisequalities (!s.isConstant[c]!) c (1 <<< tag)
    let old := ts.getD #[]
    let mut new : TSet := #[]
    for tg in tagList (TSet.tags ts ||| (1 <<< tag)) do
      new := new.push (tg, if tg == tag then id else old.get tg)
    setTermTriggers c (some new)
    let _ ← propagateTriggerTermDiseqs (1 <<< tag) (some new) diseqs

/-- `getExplanation`: the reasons of the merge of `t₁` and `t₂`, appended in
cvc5's order. The cache of pairs explained is not symmetric, as in cvc5 with
proofs on. -/
partial def getExplanation (ee : EqualityEngine) (t₁ t₂ : Nat) :
    StateM (Std.HashSet (Nat × Nat) × Array Node) Unit := do
  if (← get).1.contains (t₁, t₂) then return
  modify fun (c, r) => (c.insert (t₁, t₂), r)
  if t₁ == t₂ then return
  -- breadth-first search: (node, edge reaching it, index of its parent)
  let mut queue : Array (Nat × Option Nat × Nat) := #[(t₁, none, 0)]
  let mut idx := 0
  while idx < queue.size do
    let (cur, curEdge, _) := queue[idx]!
    let mut e := ee.graph[cur]!
    while h : e.isSome do
      let eid := e.get h
      let edge := ee.edges[eid]!
      let backward := match curEdge with
        | some ce => (eid ||| 1) == (ce ||| 1)
        | none => false
      if !backward then
        if edge.node == t₂ then
          -- reconstruct the path, from t₂ back to t₁
          let mut ce : Option Nat := some eid
          let mut ci := idx
          while h' : ce.isSome do
            let ceid := ce.get h'
            let (curNode, reachEdge, prev) := queue[ci]!
            let ed := ee.edges[ceid]!
            let edgeNode := ed.node
            match ed.type with
            | .congruence =>
              let f₁ := (ee.apps[curNode]!.map (·.1)).getD default
              let f₂ := (ee.apps[edgeNode]!.map (·.1)).getD default
              getExplanation ee f₁.a f₂.a
              getExplanation ee f₁.b f₂.b
            | .reflexivity =>
              let eqId := if curNode == ee.trueId then edgeNode else curNode
              let f := (ee.apps[eqId]!.map (·.1)).getD default
              getExplanation ee f.a f.b
            | .constants =>
              -- the non-constant side's arguments are explained to be the
              -- constants they are equal to
              let interpreted := if isConstNode ee.nodes[curNode]! then ee.nodes[edgeNode]!
                else ee.nodes[curNode]!
              let args := match interpreted with
                | .app _ cs => cs
                | _ => #[]
              for c in args do
                let cid := ee.nodeIds.getD ⟨c⟩ 0
                getExplanation ee cid (find ee cid)
            | .equality => modify fun (c, r) => (c, r.push ed.reason)
            ce := reachEdge
            ci := prev
          return
        queue := queue.push (edge.node, some eid, idx)
      e := edge.next
    idx := idx + 1

/-- The explanation of the equality or disequality of `t₁` and `t₂`
(`explainEquality`), appended to `out`. -/
def explainEquality (t₁ t₂ : Node) (polarity : Bool) (out : Array Node) : EEM (Array Node) := do
  let ee ← get
  let i₁ := ee.nodeIds.getD ⟨t₁⟩ 0
  let i₂ := ee.nodeIds.getD ⟨t₂⟩ 0
  if polarity then
    return ((getExplanation ee i₁ i₂).run ({}, out)).2.2
  match ee.diseqReasons.get? (i₁, i₂) with
  | none => return out
  | some (lo, hi) =>
    let go : StateM (Std.HashSet (Nat × Nat) × Array Node) Unit := do
      for k in [lo:hi] do
        let (a, b) := ee.deducedReasons[k]!
        getExplanation ee a b
    return (go.run ({}, out)).2.2

/-- The explanation of a predicate's value (`explainPredicate`). -/
def explainPredicate (p : Node) (polarity : Bool) (out : Array Node) : EEM (Array Node) := do
  let ee ← get
  let i := ee.nodeIds.getD ⟨p⟩ 0
  return ((getExplanation ee i (if polarity then ee.trueId else ee.falseId)).run ({}, out)).2.2

/-- The explanation of a literal as cvc5's proof equality engine computes it
(`ProofEqEngine::explainWithProof`): its assumptions, without duplicates, in
order. -/
def explainLit (lit : Node) : EEM (Array Node) := do
  let (atom, pol) := match lit with
    | .app (.kind .NOT) #[a] => (a, false)
    | _ => (lit, true)
  let raw ← match atom with
    | .app (.kind .EQUAL) #[l, r] =>
      if l == r then pure #[]
      else do
        if !pol then let _ ← areDisequal l r true
        explainEquality l r pol #[]
    | _ => explainPredicate atom pol #[]
  return raw.foldl (fun acc a => if acc.contains a then acc else acc.push a) #[]

/-- The conjunction of the assumptions (`NodeManager::mkAnd`). -/
def mkAnd (as : Array Node) : Node :=
  if as.isEmpty then Node.mkTrue
  else if as.size == 1 then as[0]!
  else Node.mkNode .AND as

/-! ## Context levels -/

/-- The counters now. -/
def counters (s : EqualityEngine) : Counters :=
  { nodes := s.nodes.size, assertedEqs := s.assertedEqs.size, lookups := s.appLookups.size,
    triggers := s.triggers.size, deducedDiseqs := s.deducedDiseqs.size,
    deducedReasons := s.deducedReasonsSize, propLog := s.propLog.size, tsetLog := s.tsetLog.size,
    done := s.done }

/-- Enter a new context level. -/
def push (s : EqualityEngine) : EqualityEngine :=
  let dt := s.dt
  let s := { s with dt := {} }
  { s with saved := s.saved.push (counters s), dt := dt.push }

/-- `undoMerge`: separate the class `c₂` from the class `c₁` it was merged
into. -/
def undoMerge (s : EqualityEngine) (c₁ c₂ : Nat) : EqualityEngine := Id.run do
  let e₁ := s.enodes[c₁]!
  let e₂ := s.enodes[c₂]!
  -- the same swap of the rings as the merge, and the size back
  let e₁' : ENode := { e₁ with next := e₂.next, size := e₁.size - e₂.size }
  let e₂' : ENode := { e₂ with next := e₁.next }
  let mut s := { s with enodes := (s.enodes.set! c₁ e₁').set! c₂ e₂' }
  let mut cur := c₂
  let mut fuel := s.enodes.size
  while fuel > 0 do
    fuel := fuel - 1
    s := { s with enodes := s.enodes.modify cur fun n => { n with find := c₂ } }
    let mut t := s.nodeTriggers[cur]!
    let mut tf := s.triggers.size
    while tf > 0 do
      tf := tf - 1
      match t with
      | none => break
      | some tid =>
        s := { s with triggers := s.triggers.modify tid fun x => { x with classId := c₂ } }
        t := s.triggers[tid]!.next
    cur := s.enodes[cur]!.next
    if cur == c₂ then break
  return s

/-- `backtrack`: undo what came after the counters `c`, in cvc5's order. -/
def backtrack (s : EqualityEngine) (c : Counters) : EqualityEngine := Id.run do
  let mut s := s
  if c.assertedEqs < s.assertedEqs.size then
    s := { s with queue := #[], qhead := 0 }
    for k in [0:s.assertedEqs.size - c.assertedEqs] do
      let i := s.assertedEqs.size - 1 - k
      if let some (l, r) := s.assertedEqs[i]! then s := undoMerge s l r
    s := { s with assertedEqs := s.assertedEqs.take c.assertedEqs }
    let keep := 2 * c.assertedEqs
    let mut i := s.edges.size
    while i ≥ keep + 2 do
      i := i - 2
      let e₁ := s.edges[i]!
      let e₂ := s.edges[i + 1]!
      s := { s with graph := (s.graph.set! e₂.node e₁.next).set! e₁.node e₂.next }
    s := { s with edges := s.edges.take keep }
  -- the trigger sets of the classes
  if c.tsetLog < s.tsetLog.size then
    for k in [0:s.tsetLog.size - c.tsetLog] do
      let (cls, old) := s.tsetLog[s.tsetLog.size - 1 - k]!
      s := { s with termTriggers := s.termTriggers.set! cls old }
    s := { s with tsetLog := s.tsetLog.take c.tsetLog }
  if c.triggers < s.triggers.size then
    for k in [0:s.triggers.size - c.triggers] do
      let i := s.triggers.size - 1 - k
      let t := s.triggers[i]!
      s := { s with nodeTriggers := s.nodeTriggers.set! t.classId t.next }
    s := { s with triggers := s.triggers.take c.triggers,
                  triggerInfos := s.triggerInfos.take c.triggers }
  if c.lookups < s.appLookups.size then
    for k in [0:s.appLookups.size - c.lookups] do
      let i := s.appLookups.size - 1 - k
      s := { s with lookup := s.lookup.erase s.appLookups[i]! }
    s := { s with appLookups := s.appLookups.take c.lookups }
  if c.nodes < s.nodes.size then
    for k in [0:s.nodes.size - c.nodes] do
      let i := s.nodes.size - 1 - k
      s := { s with nodeIds := s.nodeIds.erase ⟨s.nodes[i]!⟩ }
      if let some (orig, _) := s.apps[i]! then
        -- remove the application from the use lists of its arguments, b then a
        for x in [orig.b, orig.a] do
          let top := s.useNodes[s.useNodes.size - 1]!
          s := { s with enodes := s.enodes.modify x fun n => { n with useList := top.next },
                        useNodes := s.useNodes.pop }
    let n := c.nodes
    s := { s with nodes := s.nodes.take n, apps := s.apps.take n, nodeTriggers := s.nodeTriggers.take n,
                  isConstant := s.isConstant.take n, isEquality := s.isEquality.take n,
                  termTriggers := s.termTriggers.take n,
                  isInternal := s.isInternal.take n, graph := s.graph.take n, enodes := s.enodes.take n }
  if c.deducedDiseqs < s.deducedDiseqs.size then
    for k in [0:s.deducedDiseqs.size - c.deducedDiseqs] do
      let i := s.deducedDiseqs.size - 1 - k
      let (a, b) := s.deducedDiseqs[i]!
      s := { s with diseqReasons := (s.diseqReasons.erase (a, b)).erase (b, a) }
    s := { s with deducedReasons := s.deducedReasons.take c.deducedReasons,
                  deducedDiseqs := s.deducedDiseqs.take c.deducedDiseqs }
  s := { s with deducedReasonsSize := c.deducedReasons }
  -- the propagated disequalities, a context-dependent map
  if c.propLog < s.propLog.size then
    for k in [0:s.propLog.size - c.propLog] do
      let i := s.propLog.size - 1 - k
      let (key, old) := s.propLog[i]!
      s := { s with propagatedDiseqs := match old with
        | some v => s.propagatedDiseqs.insert key v
        | none => s.propagatedDiseqs.erase key }
    s := { s with propLog := s.propLog.take c.propLog }
  return { s with done := c.done }

/-- Return to context level `k`: restore the counters saved when leaving it. -/
def popTo (s : EqualityEngine) (k : Nat) : EqualityEngine :=
  if h : k < s.saved.size then
    let c := s.saved[k]
    -- `s` is consumed by the update, so that `backtrack` updates in place
    let dt := s.dt
    let s := backtrack { s with saved := s.saved.take k, dt := {} } c
    { s with dt := dt.popTo k }
  else s

end Telos.Solver.EE
