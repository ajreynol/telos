import Telos.Solver.EqualityEngine
import Telos.Solver.Theory.UF
import Telos.Rewriter.Rewrite

/-!
# The theory of sets

A port of cvc5's `TheorySetsPrivate` (`src/theory/sets/theory_sets_private.cpp`),
with its `SolverState`, `TermRegistry` and `InferenceManager`, with the central
equality engine, in the configuration of safe mode: no cardinality
(`setsCardExp`), no relations (`relsExp`), no universe or complement
(`setsExp`), no proxy lemmas (`setsProxyLemmas`). The higher-order operators
(`set.map`, `set.filter`, `set.fold`) and `set.choose` are not ported.

The theory reacts to the central equality engine's notifications while it
propagates (`eqNotifyNewClass`, `eqNotifyMerge`, `eqNotifyDisequal`), through
the engine's hook (`onNote`): its state is the engine's field `sets`. Its
internal facts, lemmas and conflicts are the engine's notes.

The full-effort check (`checkBasic`, the downward and upward closures,
`checkDisequalities`) runs in the theory engine's monad, through `Ops`: cvc5
preregisters the atoms of each lemma when it is sent, before the check goes on,
and the proxies' lemmas are sent in the middle of the check.

Every inference of the check is a lemma (`assertInference` with `inferType`
0): only the notifications assert internal facts to the engine.
-/

namespace Telos.Solver.Sets

open EE

def setsTheory : Theory := .THEORY_SETS

def st : EEM State := return (← get).sets

/-- `getRepresentative`: the representative of a term, or the term if the
engine does not have it. -/
def rep (n : Node) : EEM Node := do
  let s ← get
  match s.nodeIds.get? ⟨n⟩ with
  | some i => return s.nodes[find s i]!
  | none => return n

def inConflict : EEM Bool := return (← get).teConflict

/-- The element type of a set term. -/
def setElem? (n : Node) : Option TypeNode :=
  match n.typeHint with
  | some (.set E) => some E
  | _ => none

def isSet (n : Node) : Bool := (setElem? n).isSome

/-- cvc5's node order, approximated by the engine (`EE.ageLt`). -/
def idLt (a b : Node) : EEM Bool := return EE.ageLt (← get).nodeIds a b (← read).declOrder

/-- Sort pairs by their keys, in node order (a `std::map<Node, _>`). -/
def sortByKey {α : Type} (xs : Array (Node × α)) : EEM (Array (Node × α)) := do
  let ids := (← get).nodeIds
  let decl := (← read).declOrder
  return (xs.toList.mergeSort fun a b => !EE.ageLt ids b.1 a.1 decl).toArray

/-- `TheoryState::areEqual`. -/
def areEq (a b : Node) : EEM Bool := do
  if a == b then return true
  if (← hasTerm a) && (← hasTerm b) then areEqual a b else return false

/-- `TheoryState::areDisequal`. -/
def areDiseq (a b : Node) : EEM Bool := do
  if a == b then return false
  if (← hasTerm a) && (← hasTerm b) then areDisequal a b false else return false

/-! ## The classes' information (`EqcInfo`) -/

/-- `getOrMakeEqcInfo` without making: the singleton of a class, if the class
has information. -/
def info? (n : Node) : EEM (Option (Option Node)) := do
  let s ← st
  if s.hasInfo.contains ⟨n⟩ then return some (s.singleton.get? ⟨n⟩) else return none

/-- `getOrMakeEqcInfo` with `doMake`. -/
def makeInfo (n : Node) : EEM Unit :=
  modifySets fun s => if s.hasInfo.contains ⟨n⟩ then s else { s with hasInfo := s.hasInfo.insert ⟨n⟩ }

/-! ## The state's members (`SolverState`) -/

/-- `isMember`: an element of the valid members of `s` equal to `x`. -/
def isMember (x s : Node) : EEM Bool := do
  for m in (← st).memberAtoms s do
    if let .app (.kind .SET_MEMBER) #[y, _] := m then
      if ← areEq y x then return true
  return false

/-- `addMember`. -/
def addMember (r atom : Node) : EEM Unit := do
  let n := (← st).members.getD ⟨r⟩ 0
  modifySets fun s => (s.setMembers r (n + 1)).setMemberData r n atom

/-- `SolverState::merge`: the members of `t₂` move to `t₁`; with a singleton or
empty set `cset` in `t₁`, the facts (explanation, conclusion) of new members,
or the explanation of a conflict. -/
def stateMerge (t₁ t₂ : Node) (cset : Option Node) : EEM (Array (Node × Node) ⊕ Node) := do
  let s ← st
  let some n₂ := s.members.get? ⟨t₂⟩ | return .inl #[]
  let mut n₁ := s.members.getD ⟨t₁⟩ 0
  let data₂ := s.membersData.getD ⟨t₂⟩ #[]
  let mut facts := #[]
  for i in [0:n₂] do
    let m₂ := data₂[i]!
    let .app (.kind .SET_MEMBER) #[x₂, s₂] := m₂ | continue
    let data₁ := (← st).membersData.getD ⟨t₁⟩ #[]
    let mut add := true
    for j in [0:n₁] do
      if let .app (.kind .SET_MEMBER) #[x₁, _] := data₁[j]! then
        if ← areEq x₂ x₁ then add := false; break
    if !add then continue
    if let some c := cset then
      let exp := Node.mkNode .AND #[Node.eqNode s₂ c, m₂]
      match c with
      | .app (.kind .SET_SINGLETON) #[e] =>
        if e != x₂ then facts := facts.push (exp, Node.eqNode e x₂)
      | _ => return .inr exp
    modifySets fun s => s.setMemberData t₁ n₁ m₂
    n₁ := n₁ + 1
  modifySets fun s => s.setMembers t₁ n₁
  return .inl facts

/-! ## The inference manager -/

/-- Whether a literal holds in the engine (`ProofEqEngine::holds`). -/
def holds (atom : Node) (pol : Bool) : EEM Bool := do
  match atom with
  | .app (.kind .EQUAL) #[a, b] =>
    if !(← hasTerm a) || !(← hasTerm b) then return false
    if pol then areEqual a b else areDisequal a b false
  | _ =>
    if !(← hasTerm atom) then return false
    areEqual atom (if pol then Node.mkTrue else Node.mkFalse)

/-- `TheoryInferenceManager::trustedLemma`, with the cache of the lemmas sent
(by rewritten lemma). -/
def trustedLemma (lem : Node) (id : String) : EEM Bool := do
  let key : Key := ⟨Telos.rewrite lem (← read).order⟩
  if (← st).lemmaCache.contains key then return false
  modifySets fun s => { s with lemmaCache := s.lemmaCache.insert key, sentLemmas := s.sentLemmas + 1 }
  note (.lemma setsTheory id lem)
  return true

/-- The literals of a conjunction. -/
def conjuncts : Node → Array Node
  | .app (.kind .AND) cs => cs.foldl (fun acc c => acc ++ conjuncts c) #[]
  | n => if n == Node.mkTrue then #[] else #[n]
termination_by n => sizeOf n
decreasing_by all_goals (simp_wf; have := Array.sizeOf_lt_of_mem ‹_›; omega)

/-- `assertSetsConflict`: the conflict `conf`, as is (`trustedConflict`; the
theory engine explains it, `TheoryEngine::conflict`). Its explanation, for the
SAT solver, is kept (`conflict`). -/
def assertSetsConflict (conf : Node) (id : String) : EEM Unit := do
  if ← inConflict then return
  let mut assumps : Array Node := #[]
  for e in conjuncts conf do
    for a in ← explainLit e do
      if !assumps.contains a then assumps := assumps.push a
  modifySets fun s => { s with conflict := some (id, conf, assumps) }
  note (.conflict setsTheory id conf)
  modify fun s => { s with teConflict := true }

mutual
  /-- `notifyFact`: a positive membership makes the element equal to that of a
  singleton in its set's class (`SETS_MEM_EQ`), or is a conflict with the empty
  set, and becomes a member of the class. -/
  partial def notifyFact (atom : Node) (pol : Bool) : EEM Unit := do
    if ← inConflict then return
    let .app (.kind .SET_MEMBER) #[x, S] := atom | return
    if !pol then return
    let r ← rep S
    makeInfo r
    if let some (some sg) ← info? r then
      let pexp := Node.mkNode .AND #[atom, Node.eqNode S sg]
      match sg with
      | .app (.kind .SET_SINGLETON) #[e] =>
        if e != x then assertSetsFact (Node.eqNode e x) true "SETS_MEM_EQ" pexp
      | _ => assertSetsConflict pexp "SETS_MEM_EQ_CONFLICT"
    addMember r atom

  /-- `assertSetsFact` (`assertInternalFact`): the fact is asserted to the engine
  with its explanation as its reason, unless it holds already, and the theory is
  notified of it. -/
  partial def assertSetsFact (atom : Node) (pol : Bool) (id : String) (exp : Node) : EEM Unit := do
    let conc := if pol then atom else Node.notNode atom
    note (.fact setsTheory id conc exp)
    modifySets fun s => { s with sentFacts := s.sentFacts + 1 }
    if !(← holds atom pol) then
      -- (with the premises of the edge it makes)
      modifySets fun s => { s with facts := addFact s.facts conc id exp }
      match atom with
      | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol exp
      | _ => let _ ← assertPredicate atom pol exp
    notifyFact atom pol
end

/-- `SolverState::isEntailed`. -/
partial def isEntailed (n : Node) (pol : Bool) : EEM Bool := do
  match n with
  | .app (.kind .NOT) #[a] => isEntailed a (!pol)
  | .app (.kind .EQUAL) #[a, b] => if pol then areEq a b else areDiseq a b
  | .app (.kind .SET_MEMBER) #[x, S] =>
    if ← areEq n (if pol then Node.mkTrue else Node.mkFalse) then return true
    if pol && (← hasTerm S) then
      if ← isMember x (← rep S) then return true
    return false
  | .app (.kind k) cs =>
    if k == .AND || k == .OR then
      let conj := (k == .AND) == pol
      for c in cs do
        if (← isEntailed c pol) != conj then return !conj
      return conj
    return false
  | _ =>
    if n == Node.mkTrue then return pol
    if n == Node.mkFalse then return !pol
    return false

/-- `setupAndAddPendingLemma`: `(=> exp conc)` (or `conc`), pending; a
conclusion `false` is a conflict. -/
def addPendingLemma (exp conc : Node) (id : String) : EEM Unit := do
  if conc == Node.mkFalse then
    assertSetsConflict exp id
    return
  let lem := if exp == Node.mkTrue then conc else Node.mkNode .IMPLIES #[exp, conc]
  modifySets fun s => { s with pendingLemmas := s.pendingLemmas.push { lem, id } }

/-- The explanation of a list of literals (`mkAnd`). -/
def mkExp (exp : Array Node) : Node :=
  if exp.isEmpty then Node.mkTrue else if exp.size == 1 then exp[0]! else Node.mkNode .AND exp

/-- `assertInference` with `inferType` 0 or 1 (`assertFactRec`): a pending
lemma, unless the fact is entailed. -/
def assertInference (fact : Node) (id : String) (exp : Array Node) : EEM Unit := do
  if ← isEntailed fact true then return
  addPendingLemma (mkExp exp) fact id

/-- `TheoryInferenceManager::reset`. -/
def reset : EEM Unit := modifySets fun s => { s with sentFacts := 0, sentLemmas := 0 }

def hasSent : EEM Bool := do
  let s ← st
  return (← inConflict) || s.sentLemmas > 0 || s.sentFacts > 0

def hasPending : EEM Bool := return !(← st).pendingLemmas.isEmpty

/-! ## Notifications -/

/-- `eqNotifyNewClass`: a singleton or empty set is the singleton of its class. -/
def notifyNewClass (t : Node) : EEM Unit := do
  match t.getKind with
  | .SET_SINGLETON | .SET_EMPTY =>
    makeInfo t
    modifySets fun s => s.setSingleton t (some t)
  | _ => pure ()

/-- `eqNotifyMerge`: the singletons of the classes (`SETS_SINGLETON_EQ`, or a
conflict `SETS_EQ_CONFLICT`), then the members (`SETS_EQ_MEM`, or a conflict
`SETS_EQ_MEM_CONFLICT`). -/
def notifyMerge (t₁ t₂ : Node) : EEM Unit := do
  if (← inConflict) || !isSet t₁ then return
  let mut s₁ : Option Node := none
  let mut s₂ : Option Node := none
  if let some e₂ ← info? t₂ then
    s₂ := e₂
    match ← info? t₁ with
    | some e₁ =>
      s₁ := e₁
      if let (some a, some b) := (s₁, s₂) then
        if a.getKind == b.getKind then
          match a, b with
          | .app _ #[x], .app _ #[y] =>
            assertSetsFact (Node.eqNode x y) true "SETS_SINGLETON_EQ" (Node.eqNode a b)
          | _, _ => pure ()
        else
          assertSetsConflict (Node.eqNode a b) "SETS_EQ_CONFLICT"
          return
    | none =>
      makeInfo t₁
      modifySets fun s => s.setSingleton t₁ s₂
  let checkSingleton := if s₂.isNone then s₁ else none
  match ← stateMerge t₁ t₂ checkSingleton with
  | .inr conf => assertSetsConflict conf "SETS_EQ_MEM_CONFLICT"
  | .inl facts =>
    for (exp, conc) in facts do
      assertSetsFact conc true "SETS_EQ_MEM" exp

/-- `eqNotifyDisequal`: a disequality of sets is recorded. -/
def notifyDisequal (t₁ t₂ : Node) : EEM Unit := do
  if isSet t₁ then modifySets fun s => s.addDeq (Node.eqNode t₁ t₂)

/-- The theory's handling of the central equality engine's notifications. -/
def handle : Note → EEM Unit
  | .newClass t => notifyNewClass t
  | .merge t₁ t₂ => notifyMerge t₁ t₂
  | .disequal t₁ t₂ _ => notifyDisequal t₁ t₂
  | _ => pure ()

/-- The hook of the central equality engine (`EE.Ctx.onNote`): the
notification handled with the context `c`. The facts the handlers assert are
merged by the propagation that notified them, with the theories' hook. -/
def onNote (c : Ctx) (n : Note) (ee : EqualityEngine) : EqualityEngine :=
  if ee.sets.enabled then (((handle n).run c).run ee).2 else ee

/-! ## Facts and registration -/

/-- `Theory::check`'s processing of one fact: asserted to the engine, with the
fact as its reason, then notified. -/
def assertFact (fact : Node) : EEM Unit := do
  let (atom, pol) := match fact with
    | .app (.kind .NOT) #[a] => (a, false)
    | _ => (fact, true)
  match atom with
  | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol fact
  | _ => let _ ← assertPredicate atom pol fact
  notifyFact atom pol

/-- `SetReduction::mkChooseMemberAxiom`: for `n = (set.choose A)`, `A` is empty
or has `n`. -/
def mkChooseMemberAxiom (n A : Node) (E : TypeNode) : Node :=
  Node.orNode (Node.eqNode A (.const (.emptySet E))) (Node.mkNode .SET_MEMBER #[n, A])

/-- `preRegisterTerm`: equalities and memberships are trigger predicates; the
membership lemma of a `set.choose` is sent (`SETS_CHOOSE_MEMBER`). -/
def preRegisterTerm (n : Node) : EEM Unit := do
  match n with
  | .app (.kind .EQUAL) _ | .app (.kind .SET_MEMBER) _ => UF.addTriggerPredicate n
  | .app (.kind .SET_CHOOSE) #[A] =>
    addTerm n
    if let some (.set E) := A.typeHint then
      let _ ← trustedLemma (mkChooseMemberAxiom n A E) "SETS_CHOOSE_MEMBER"
  | _ => addTerm n

/-- The kinds the theory adds to the equality engine (`finishInit`). -/
def congruenceKind (k : Kind) : Bool :=
  k == .SET_SINGLETON || k == .SET_UNION || k == .SET_INTER || k == .SET_MINUS ||
    k == .SET_MEMBER || k == .SET_SUBSET || k == .SET_CHOOSE

/-! ## The check (`checkBasic`, closures, disequalities) -/

/-- What the check needs from the theory engine. -/
structure Ops (m : Type → Type) where
  /-- Run an operation of the equality engine, process its notes, and register
  the atoms of the lemmas sent (`TheoryEngine::lemma`). -/
  run : {α : Type} → EEM α → m α

/-- The classes of the engine, from index `i`: the first representative at or
after `i`, and its index (`EqClassesIterator`, which sees the classes created
while it runs). -/
def nextClass (i : Nat) : EEM (Option (Nat × Node)) := do
  let s ← get
  let mut j := i
  while j < s.nodes.size do
    if find s j == j && !s.isInternal[j]! then return some (j, s.nodes[j]!)
    j := j + 1
  return none

/-- The terms of a class (`EqClassIterator`), from its representative. -/
def classTerms (r : Node) : EEM (Array Node) := do
  let s ← get
  let some i := s.nodeIds.get? ⟨r⟩ | return #[r]
  let mut out := #[]
  let mut j := i
  repeat
    if !s.isInternal[j]! then out := out.push s.nodes[j]!
    j := s.enodes[j]!.next
    if j == i then break
  return out

/-- Insert into a sorted-by-insertion association list, unless present. -/
def assocInsert {α : Type} (xs : Array (Node × α)) (k : Node) (v : α) : Array (Node × α) × Bool :=
  if xs.any (·.1 == k) then (xs, false) else (xs.push (k, v), true)

/-- Add `n` to the non-variable sets of `r`. -/
def Check.addNvar (c : Check) (r n : Node) : Check :=
  { c with nvarSets := c.nvarSets.insert ⟨r⟩ ((c.nvarSets.getD ⟨r⟩ #[]).push n) }

/-- Set `bopIndex[k][a][b] := n`. -/
def Check.setBop (c : Check) (k : Kind) (a b n : Node) : Check :=
  let bop := c.bopIndex
  let ki := (bop.findIdx? (·.1 == k)).getD bop.size
  let bop := if ki == bop.size then bop.push (k, #[]) else bop
  let rows := bop[ki]!.2
  let row := ((rows.find? (·.1 == a)).map (·.2)).getD #[]
  let row := match row.findIdx? (·.1 == b) with
    | some j => row.set! j (b, n)
    | none => row.push (b, n)
  let rows := match rows.findIdx? (·.1 == a) with
    | some j => rows.set! j (a, row)
    | none => rows.push (a, row)
  { c with bopIndex := bop.set! ki (k, rows) }

/-- `bopIndex[k][a][b]`. -/
def Check.getBop (c : Check) (k : Kind) (a b : Node) : Option Node := do
  let (_, rows) ← c.bopIndex.find? (·.1 == k)
  let (_, row) ← rows.find? (·.1 == a)
  let (_, n) ← row.find? (·.1 == b)
  return n

/-- `SolverState::registerTerm`. -/
def registerTerm (r n : Node) : EEM Unit := do
  let c := (← st).check
  let c ← match n with
    | .app (.kind .SET_MEMBER) #[x, S] =>
      if r == Node.mkTrue || r == Node.mkFalse then
        let s ← rep S
        let xr ← rep x
        let pos := r == Node.mkTrue
        let mems := (if pos then c.posMems else c.negMems).getD ⟨s⟩ #[]
        let (mems, _) := assocInsert mems xr n
        let c := if pos then { c with posMems := c.posMems.insert ⟨s⟩ mems }
          else { c with negMems := c.negMems.insert ⟨s⟩ mems }
        let idx := c.membersIndex.getD ⟨s⟩ {}
        pure (if idx.contains ⟨xr⟩ then c else
          { c with membersIndex := c.membersIndex.insert ⟨s⟩ (idx.insert ⟨xr⟩ n), careTerms := c.careTerms.push n })
      else pure c
    | .app (.kind .SET_SINGLETON) #[e] =>
      let re ← rep e
      let c := match c.singletonIndex.get? ⟨re⟩ with
        | none => { c with singletonIndex := c.singletonIndex.insert ⟨re⟩ n,
                           eqcSingleton := c.eqcSingleton.insert ⟨r⟩ n,
                           careTerms := c.careTerms.push n }
        | some o => { c with congruent := c.congruent.insert ⟨n⟩ o }
      pure (c.addNvar r n)
    | .app (.kind k) #[a, b] =>
      if k == .SET_UNION || k == .SET_INTER || k == .SET_MINUS then
        let r₁ ← rep a
        let r₂ ← rep b
        let c := match c.getBop k r₁ r₂ with
          | none => c.setBop k r₁ r₂ n
          | some o =>
            -- congruent; also indexed by its own arguments
            { (c.setBop k a b n) with congruent := c.congruent.insert ⟨n⟩ o }
        pure (c.addNvar r n)
      else pure (if isSet n then varOf c r n else c)
    | .const (.emptySet T) =>
      let c := if c.eqcEmptyset.any (·.1 == .set T) then c
        else { c with eqcEmptyset := c.eqcEmptyset.push (.set T, r) }
      pure (c.addNvar r n)
    | .app (.kind .SET_CHOOSE) _ =>
      -- (for the care graph; a leaf otherwise)
      let c := { c with careTerms := c.careTerms.push n }
      pure (if isSet n then varOf c r n else c)
    | _ => pure (if isSet n then varOf c r n else c)
  modifySets fun s => { s with check := c }
where
  /-- A leaf of set type: the variable of its class. -/
  varOf (c : Check) (r n : Node) : Check :=
    if c.varSet.contains ⟨r⟩ then c else { c with varSet := c.varSet.insert ⟨r⟩ n }

/-- `SolverState::reset`. -/
def resetState : EEM Unit := modifySets fun s => { s with check := {} }

/-- `getMembers`, in node order. -/
def getMembers (r : Node) : EEM (Array (Node × Node)) := do
  sortByKey ((← st).check.posMems.getD ⟨r⟩ #[])

def getNegMembers (r : Node) : EEM (Array (Node × Node)) := do
  sortByKey ((← st).check.negMems.getD ⟨r⟩ #[])

/-- `addEqualityToExp`. -/
def addEq (a b : Node) (exp : Array Node) : Array Node :=
  if a != b then exp.push (Node.eqNode a b) else exp

section
variable {m : Type → Type} [Monad m] (ops : Ops m)

/-- `doPendingLemmas`: each pending lemma is sent, and its atoms registered,
in turn. -/
def doPendingLemmas : m Unit := do
  let mut i := 0
  repeat
    let some l ← ops.run do return (← st).pendingLemmas[i]? | break
    let _ ← ops.run (trustedLemma l.lem l.id)
    i := i + 1
  ops.run (modifySets fun s => { s with pendingLemmas := #[] })

/-- `TermRegistry::getProxy`: the purification skolem of a non-variable set,
with its lemmas (`SETS_PROXY`, and `SETS_PROXY_SINGLETON` for a singleton),
each sent at once. -/
def getProxy (n : Node) : m Node := do
  match n.getKind with
  | .SET_EMPTY | .SET_SINGLETON | .SET_INTER | .SET_MINUS | .SET_UNION =>
    if let some k ← ops.run do return (← st).proxy.get? ⟨n⟩ then return k
    let k := Node.skolem .PURIFY #[n]
    ops.run (modifySets fun s => { s with proxy := s.proxy.insert ⟨n⟩ k })
    let _ ← ops.run (trustedLemma (Node.eqNode k n) "SETS_PROXY")
    if let .app (.kind .SET_SINGLETON) #[e] := n then
      let _ ← ops.run (trustedLemma (Node.mkNode .SET_MEMBER #[e, k]) "SETS_PROXY_SINGLETON")
    return k
  | _ => return n

/-- The registration of `checkBasic`: every relevant term of every class. -/
def registerAll (relevant : Std.HashSet Key) : m Unit := do
  let mut i := 0
  repeat
    let some (j, eqc) ← ops.run (nextClass i) | break
    i := j + 1
    if isSet eqc then ops.run (modifySets fun s => { s with check := { s.check with setEqc := s.check.setEqc.push eqc } })
    for n in ← ops.run (classTerms eqc) do
      if !relevant.contains ⟨n⟩ then continue
      ops.run (registerTerm eqc n)
      if n.getKind == .SET_SINGLETON then
        let _ ← getProxy ops n

/-- `checkDownwardsClosure`: a member of a class is a member of each
non-variable set of the class (`SETS_DOWN_CLOSURE`), rewritten. -/
def checkDownwardsClosure : m Unit := do
  for s in (← ops.run st).check.setEqc do
    let nvsets := (← ops.run st).check.nvarSets.getD ⟨s⟩ #[]
    if nvsets.isEmpty then continue
    let smem ← ops.run (getMembers s)
    for nv in nvsets do
      for (_, mem) in smem do
        let .app (.kind .SET_MEMBER) #[x, S] := mem | continue
        if S != nv then
          let o ← ops.run do return (← read).order
          let nmem := Telos.rewrite (Node.mkNode .SET_MEMBER #[x, nv]) o
          ops.run (assertInference nmem "SETS_DOWN_CLOSURE" #[mem, Node.eqNode S nv])
          if ← ops.run inConflict then return

/-- `checkUpwardsClosure`: the members of the arguments of a union,
intersection or difference (`SETS_UP_CLOSURE`, `SETS_UP_CLOSURE_2`). -/
def checkUpwardsClosure : m Unit := do
  let bop := (← ops.run st).check.bopIndex
  for k in [Kind.SET_UNION, .SET_INTER, .SET_MINUS] do
    let some (_, rows) := bop.find? (·.1 == k) | continue
    for (a, row) in ← ops.run (sortByKey rows) do
      let r₁ ← ops.run (rep a)
      let r₁mem ← ops.run (getMembers r₁)
      if r₁mem.isEmpty && k != .SET_UNION then continue
      for (b, term) in ← ops.run (sortByKey row) do
        let r₂ ← ops.run (rep b)
        let r₂mem ← ops.run (getMembers r₂)
        let r₂nmem ← ops.run (getNegMembers r₂)
        if r₂mem.isEmpty && k == .SET_INTER then continue
        let .app _ #[t₀, t₁] := term | continue
        for (xr, m₁) in r₁mem do
          let .app (.kind .SET_MEMBER) #[x, S₁] := m₁ | continue
          let mut exp := addEq t₀ S₁ #[m₁]
          let mut valid := false
          if k == .SET_UNION then valid := true
          else if k == .SET_INTER then
            match r₂mem.find? (·.1 == xr) with
            | some (_, m₂) =>
              let .app (.kind .SET_MEMBER) #[y, S₂] := m₂ | continue
              exp := addEq x y (addEq t₁ S₂ (exp.push m₂))
              valid := true
            | none =>
              if !(r₂nmem.any (·.1 == xr)) then
                exp := exp.push (Node.mkNode .SET_MEMBER #[x, t₁])
                valid := true
          else
            if !(r₂mem.any (·.1 == xr)) then
              exp := exp.push (Node.notNode (Node.mkNode .SET_MEMBER #[x, t₁]))
              valid := true
          if valid then
            let rr ← ops.run (rep term)
            if !(← ops.run (isMember x rr)) then
              let kk ← getProxy ops term
              ops.run (assertInference (Node.mkNode .SET_MEMBER #[x, kk]) "SETS_UP_CLOSURE" exp)
              if ← ops.run inConflict then return
        if k == .SET_UNION then
          for (_, m₂) in r₂mem do
            let .app (.kind .SET_MEMBER) #[x, S₂] := m₂ | continue
            let rr ← ops.run (rep term)
            if !(← ops.run (isMember x rr)) then
              let exp := addEq t₁ S₂ #[m₂]
              let r ← getProxy ops term
              ops.run (assertInference (Node.mkNode .SET_MEMBER #[x, r]) "SETS_UP_CLOSURE_2" exp)
              if ← ops.run inConflict then return

/-- `checkBasic`. -/
def checkBasic (relevant : Std.HashSet Key) : m Unit := do
  registerAll ops relevant
  if ← ops.run hasSent then return
  doPendingLemmas ops
  if ← ops.run hasSent then return
  checkDownwardsClosure ops
  doPendingLemmas ops
  if ← ops.run hasSent then return
  checkUpwardsClosure ops
  doPendingLemmas ops

/-- `isSetDisequalityEntailedInternal`. -/
def deqEntailedInternal (a b : Node) (re : Option Node) : EEM Bool := do
  let c := (← st).check
  let some ma := c.posMems.get? ⟨a⟩ | return false
  if some b == re then return !ma.isEmpty
  let sb := c.eqcSingleton.get? ⟨b⟩
  let nb := c.negMems.get? ⟨b⟩
  let mut prev : Array Node := #[]
  for (x, _) in ← sortByKey ma do
    match sb with
    | some (.app _ #[e]) =>
      if ← areDiseq x e then return true
      for p in prev do
        if ← areDiseq x p then return true
    | _ =>
      if let some nbs := nb then
        for (y, _) in nbs do
          if ← areEq x y then return true
    prev := prev.push x
  return false

/-- `isSetDisequalityEntailed`. -/
def deqEntailed (r₁ r₂ : Node) : EEM Bool := do
  let c := (← st).check
  let re := match r₁.typeHint with
    | some T => (c.eqcEmptyset.find? (·.1 == T)).map (·.2)
    | none => none
  if ← deqEntailedInternal r₁ r₂ re then return true
  deqEntailedInternal r₂ r₁ re

/-- `checkDisequalities`: a disequality of sets that is not entailed gets an
element in exactly one of them (`SETS_DEQ`), once. -/
def checkDisequalities : m Unit := do
  let mut i := 0
  repeat
    let some (deq, active) ← ops.run do return (← st).deq[i]? | break
    let j := i
    i := i + 1
    if !active then continue
    let .app (.kind .EQUAL) #[a, b] := deq | continue
    let r₁ ← ops.run (rep a)
    let r₂ ← ops.run (rep b)
    let isSat ← ops.run (deqEntailed r₁ r₂)
    ops.run (modifySets fun s => s.deqOff j)
    if isSat then continue
    if (← ops.run st).termProcessed.contains ⟨deq⟩ then continue
    ops.run (modifySets fun s => { s with
      termProcessed := (s.termProcessed.insert ⟨deq⟩).insert ⟨Node.eqNode b a⟩ })
    let x := Node.skolem .SETS_DEQ_DIFF #[a, b]
    let mem₁ := Node.mkNode .SET_MEMBER #[x, a]
    let mem₂ := Node.mkNode .SET_MEMBER #[x, b]
    let mdeq := Node.notNode (Node.eqNode mem₁ mem₂)
    ops.run (assertInference mdeq "SETS_DEQ" #[Node.notNode deq])
    doPendingLemmas ops
    if ← ops.run hasSent then return

/-- `TheorySetsPrivate::postCheck` at full effort, with the strategy of safe
mode: `fullEffortReset`, `checkBasic`, then, if nothing was sent,
`checkDisequalities`; repeated while facts were asserted and no lemma was sent
(`StrategyBase::postCheck`). `needCheck` is the theory engine's
`Valuation::needCheck`. -/
def postCheck (relevant : Std.HashSet Key) (needCheck : m Bool) : m Unit := do
  if (← ops.run inConflict) || (← needCheck) then return
  repeat
    ops.run reset
    -- the strategy: reset, basic, (break), disequalities
    ops.run (do reset; resetState; modifySets fun s => { s with pendingLemmas := #[] })
    checkBasic ops relevant
    if !(← ops.run inConflict) && !(← ops.run hasSent) && !(← ops.run hasPending) then
      checkDisequalities ops
    let hadPending := (← ops.run hasPending) || (← ops.run st).sentFacts > 0
    doPendingLemmas ops
    let sentLemma := (← ops.run st).sentLemmas > 0
    if (← ops.run inConflict) || sentLemma || !hadPending then break

end

end Telos.Solver.Sets
