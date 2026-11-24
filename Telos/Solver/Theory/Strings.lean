import Telos.Solver.EqualityEngine
import Telos.Solver.Theory.UF
import Telos.Rewriter.Rewrite

/-!
# The theory of strings

A port of cvc5's `TheoryStrings` (`src/theory/strings/`), with the central
equality engine, in the configuration of safe mode (see `docs/theory-engine-plan.md`,
Stage 9). This file has, so far, stage 1's registration of terms
(`TermRegistry`): the length lemmas of string terms (`STRINGS_REGISTER_TERM`,
with a proxy variable, the purification skolem of the term, for constants and
concatenations; `STRINGS_REGISTER_TERM_ATOMIC`, the split of the length of an
atomic term, with its preferred phases), sent as the terms are preregistered,
with eager registration (`stringEagerReg`).

The theory's state is the engine's field `strings`. Registration runs in the
theory engine's monad, through `Ops`: cvc5 sends a lemma while it preregisters a
term, and the lemma's atoms are preregistered then, before the next term.
-/

namespace Telos.Solver.Strings

open EE

def stringsTheory : Theory := .THEORY_STRINGS

def st : EEM State := return (← get).strings

/-- A term of type `String` or of a sequence type. -/
def isStringLike (n : Node) : Bool :=
  match n.typeHint with
  | some .string | some (.sequence _) => true
  | _ => false

/-- The empty string (`Word::mkEmptyWord`). -/
def emptyWord : Node := .const (.string [])

/-- The empty word of the type of `t` (`Word::mkEmptyWord`). -/
def emptyOf (t : Node) : Node :=
  match t.typeHint with
  | some (.sequence T) => .const (.emptySeq T)
  | _ => emptyWord

/-- An empty word. -/
def isEmptyWord (n : Node) : Bool :=
  match n with
  | .const (.string []) | .const (.emptySeq _) => true
  | _ => false

/-- `utils::isConstantLike`: a constant, or a unit. (A sequence of values of more
than one element, a constant of cvc5's, is a concatenation of units here.) -/
def isConstLike (n : Node) : Bool := n.isConst || n.getKind == .SEQ_UNIT

def mkLen (n : Node) : Node := Node.mkNode .STRING_LENGTH #[n]

def intConst (k : Int) : Node := .const (.integer k)

/-- The rewrite of a node the theory built, in cvc5's node order (its nodes
created after those numbered). -/
def rw (n : Node) : EEM Node := do
  if let some r := (← st).rwCache.get? ⟨n⟩ then return r
  let r := Telos.rewrite n (← numbered n)
  modifyStrings fun s =>
    let m := s.rwCache
    let s := { s with rwCache := {} }
    { s with rwCache := m.insert ⟨n⟩ r }
  return r

/-- `utils::flattenOp` for `AND`: the conjuncts of `n` added to `acc`, left to
right, without duplicates. -/
partial def flattenAnd (n : Node) (acc : Array Node) : Array Node :=
  match n with
  | .app (.kind .AND) cs => cs.foldl (fun a c => flattenAnd c a) acc
  | _ => if acc.contains n then acc else acc.push n

/-! ## The inference manager -/

/-- `TheoryInferenceManager::trustedLemma`, with the cache of the lemmas sent
(by rewritten lemma). -/
def trustedLemma (lem : Node) (id : String) : EEM Bool := do
  let key : Key := ⟨← rw lem⟩
  if (← st).lemmaCache.contains key then return false
  modifyStrings fun s => { s with lemmaCache := s.lemmaCache.insert key, sentLemmas := s.sentLemmas + 1 }
  note (.lemma stringsTheory id lem)
  return true

/-! ## The eager solver (`EagerSolver`)

The bounds of a class (`EqcInfo.firstBound`, `secondBound`): for strings, the
terms that give its longest known constant prefix and suffix; for integers,
the terms that give its greatest lower and least upper bound (a length term,
by the constant bounds of its argument's length, or a constant). A merge whose
bounds clash is a conflict, pending until the fact asserted is processed
(`STRINGS_PREFIX_CONFLICT`, `STRINGS_ARITH_BOUND_CONFLICT`). -/

def word? : Node → Option (List Nat)
  | .const (.string w) => some w
  | .const (.emptySeq _) => some []
  | _ => none

def intValue? : Node → Option Int
  | .const (.integer k) => some k
  | .const (.rational q) => if q.den == 1 then some q.num else none
  | _ => none

/-- `utils::getConstantComponent`. -/
def constantComponent (t : Node) : Option Node :=
  match t with
  | .app (.kind .STRING_TO_REGEXP) #[c] => if c.isConst then some c else none
  | _ => if t.isConst then some t else none

/-- `utils::getConstantEndpoint`. -/
def constantEndpoint (e : Node) (isSuf : Bool) : Option Node :=
  let e := match e with
    | .app (.kind .STRING_IN_REGEXP) #[_, r] => r
    | _ => e
  match e with
  | .app (.kind k) cs =>
    if (k == .STRING_CONCAT || k == .REGEXP_CONCAT) && cs.size > 0 then
      constantComponent cs[if isSuf then cs.size - 1 else 0]!
    else constantComponent e
  | _ => constantComponent e

/-- `SkolemManager::getOriginalForm`: purification skolems replaced by their
terms. -/
partial def originalForm (t : Node) : Node :=
  match t with
  | .skolem .PURIFY #[u] => originalForm u
  | .app op cs => .app op (cs.map originalForm)
  | _ => t

/-- `ArithEntail::getConstantBoundLength`: a constant lower (or upper) bound of
the length of a string term. -/
partial def constantBoundLength (s : Node) (isLower : Bool) : Option Int :=
  let r : Option Int := match s with
    | .const (.string w) => some w.length
    | .const (.emptySeq _) => some 0
    | .app (.kind .SEQ_UNIT) _ => some 1
    | .app (.kind .STRING_CONCAT) cs => Id.run do
      let mut sum : Int := 0
      for c in cs do
        match constantBoundLength c isLower with
        | some b => sum := sum + b
        | none => if isLower then continue else return none
      return if !isLower || sum != 0 then some sum else none
    | _ => none
  if r.isNone && isLower then some 0 else r

/-- `getBoundForLength` (a length term; the bounds of regular expressions come
with them, stage 3). -/
def boundForLength (t : Node) (isLower : Bool) : Option Int :=
  match t with
  | .app (.kind .STRING_LENGTH) #[a] => constantBoundLength (originalForm a) isLower
  | _ => none

/-- `EqcInfo::mkMergeConflict`. -/
def mkMergeConflict (t prev : Node) (isArith : Bool) : Node := Id.run do
  let mut ccs : Array Node := #[]
  let mut r : Array Node := #[]
  for tp in [t, prev] do
    match tp with
    | .app (.kind .STRING_IN_REGEXP) #[a, _] =>
      ccs := ccs.push tp
      r := r.push (if isArith then mkLen a else a)
    | _ => r := r.push tp
  if r[0]! != r[1]! then ccs := ccs.push (Node.eqNode r[0]! r[1]!)
  return if ccs.size == 1 then ccs[0]! else Node.mkNode .AND ccs

/-- `EqcInfo::addEndpointConst`: the information with `t` as a bound of its
constant prefix (suffix) `c`, or a conflict. -/
def addEndpointConst (e : EqcInfo) (t : Node) (c : Option Node) (isSuf : Bool) :
    EqcInfo × Option Node := Id.run do
  let prev := if isSuf then e.secondBound else e.firstBound
  if let some prev := prev then
    let some prevC := constantEndpoint prev isSuf | return (e, none)
    let some c := c.orElse fun _ => constantEndpoint t isSuf | return (e, none)
    let mut conflict := false
    if c != prevC then
      let pw := (word? prevC).getD []
      let cw := (word? c).getD []
      let (pvs, cvs) := (pw.length, cw.length)
      if pvs == cvs || (pvs > cvs && t.isConst) || (cvs > pvs && prev.isConst) then
        conflict := true
      else
        let (larges, smalls) := if pvs > cvs then (pw, cw) else (cw, pw)
        conflict := if isSuf then !smalls.isSuffixOf larges else !smalls.isPrefixOf larges
      if !conflict && (pvs > cvs || prev.isConst) then return (e, none)
    else if !t.isConst then return (e, none)
    if conflict then return (e, some (mkMergeConflict t prev false))
  let e := if isSuf then { e with secondBound := some t } else { e with firstBound := some t }
  return (e, none)

/-- `EagerSolver::addArithmeticBound`: the information with `t` as a lower
(upper) bound, or a conflict. -/
def addArithmeticBound (e : EqcInfo) (t : Node) (isLower : Bool) : EqcInfo × Option Node := Id.run do
  let bound (n : Node) (lower : Bool) : Option Int :=
    if n.isConst then intValue? n else boundForLength n lower
  let some br := bound t isLower | return (e, none)
  if let some prev := (if isLower then e.firstBound else e.secondBound) then
    if let some prevbr := bound prev isLower then
      if prevbr == br || (br < prevbr) == isLower then return (e, none)
  if let some prevo := (if isLower then e.secondBound else e.firstBound) then
    if let some prevobr := bound prevo !isLower then
      if prevobr != br && (prevobr < br) == isLower then
        return (e, some (mkMergeConflict t prevo true))
  let e := if isLower then { e with firstBound := some t } else { e with secondBound := some t }
  return (e, none)

/-- `SolverState::setPendingMergeConflict`. -/
def setPendingMergeConflict (conf : Node) (id : String) : EEM Unit :=
  let premises := match conf with
    | .app (.kind .AND) cs => cs
    | c => #[c]
  modifyStrings fun s => s.setPendingConflict id premises

/-- `addEndpointsToEqcInfo`: the constant endpoints of a concatenation `concat`
(by `t`) added to the information of `eqc`. -/
def addEndpointsToEqcInfo (t concat eqc : Node) : EEM Bool := do
  let .app _ cs := concat | return false
  if cs.size == 0 then return false
  for r in [0, 1] do
    let some c := constantComponent cs[if r == 0 then 0 else cs.size - 1]! | continue
    let e := ((← st).getEqcInfo? eqc).getD {}
    let (e, conf) := addEndpointConst e t (some c) (r == 1)
    modifyStrings fun s => s.setEqcInfo eqc e
    if let some conf := conf then
      setPendingMergeConflict conf "STRINGS_PREFIX_CONFLICT"
      return true
  return false

/-- The representative of a term, if the engine has it. -/
def rep (a : Node) : EEM Node := do
  let s ← get
  return match s.nodeIds.get? ⟨a⟩ with
    | some i => s.nodes[find s i]!
    | none => a

/-! ## Notifications -/

def eqcInfo? (n : Node) : EEM (Option EqcInfo) := return (← st).getEqcInfo? n

/-- `eqNotifyNewClass`: a length (code) term is the length term (code term) of
its argument's class; then the eager solver's bounds. -/
def notifyNewClass (t : Node) : EEM Unit := do
  match t with
  | .app (.kind .STRING_LENGTH) #[a] | .app (.kind .STRING_TO_CODE) #[a] =>
    let r ← rep a
    let e := ((← st).getEqcInfo? r).getD {}
    let e := if t.getKind == .STRING_LENGTH then { e with lengthTerm := some t } else { e with codeTerm := some a }
    modifyStrings fun st => st.setEqcInfo r e
  | _ => pure ()
  -- `EagerSolver::eqNotifyNewClass`
  match t with
  | .app (.kind .STRING_LENGTH) _ =>
    for lower in [true, false] do
      if (boundForLength t lower).isSome then
        let e := ((← st).getEqcInfo? t).getD {}
        let e := if lower then { e with firstBound := some t } else { e with secondBound := some t }
        modifyStrings fun st => st.setEqcInfo t e
  | .app (.kind .STRING_CONCAT) _ => let _ ← addEndpointsToEqcInfo t t t
  | _ =>
    if t.isConst && (isStringLike t || t.typeHint == some .integer) then
      let e := ((← st).getEqcInfo? t).getD {}
      modifyStrings fun st => st.setEqcInfo t { e with firstBound := some t, secondBound := some t }

/-- `eqNotifyMerge`: the eager solver's check of the bounds, then the
information of the class of `t₂` added to that of `t₁`. -/
def notifyMerge (t₁ t₂ : Node) : EEM Unit := do
  let some e₂ ← eqcInfo? t₂ | return
  let mut e₁ := (← eqcInfo? t₁).getD {}
  -- `checkForMergeConflict`
  let str := isStringLike t₁
  for i in [0, 1] do
    let some n := (if i == 0 then e₂.firstBound else e₂.secondBound) | continue
    let (e, conf) := if str then addEndpointConst e₁ n none (i == 1) else addArithmeticBound e₁ n (i == 0)
    e₁ := e
    if let some conf := conf then
      setPendingMergeConflict conf (if str then "STRINGS_PREFIX_CONFLICT" else "STRINGS_ARITH_BOUND_CONFLICT")
      break
  e₁ := { e₁ with
    lengthTerm := e₂.lengthTerm.orElse fun _ => e₁.lengthTerm
    codeTerm := e₂.codeTerm.orElse fun _ => e₁.codeTerm
    cardinalityLemK := max e₁.cardinalityLemK e₂.cardinalityLemK
    normalizedLength := e₂.normalizedLength.orElse fun _ => e₁.normalizedLength }
  modifyStrings fun s => s.setEqcInfo t₁ e₁

def handle : Note → EEM Unit
  | .newClass t => notifyNewClass t
  | .merge t₁ t₂ => notifyMerge t₁ t₂
  | _ => pure ()

/-- The hook of the central equality engine (`EE.Ctx.onNote`). -/
def onNote (c : Ctx) (n : Note) (ee : EqualityEngine) : EqualityEngine :=
  if ee.strings.enabled then (((handle n).run c).run ee).2 else ee

/-- The kinds the theory adds to the equality engine (`finishInit`), all with
eager evaluation (`stringEagerEval`) but `seq.nth`. -/
def congruenceKind (k : Kind) : Bool :=
  k == .STRING_LENGTH || k == .STRING_CONCAT || k == .STRING_IN_REGEXP || k == .STRING_TO_CODE ||
    k == .STRING_CONTAINS || k == .STRING_LEQ ||
    k == .STRING_SUBSTR || k == .STRING_UPDATE || k == .STRING_ITOS || k == .STRING_STOI ||
    k == .STRING_INDEXOF || k == .STRING_INDEXOF_RE || k == .STRING_REPLACE ||
    k == .STRING_REPLACE_ALL || k == .STRING_REPLACE_RE || k == .STRING_REPLACE_RE_ALL ||
    k == .STRING_TO_LOWER || k == .STRING_TO_UPPER || k == .STRING_REV || k == .SEQ_UNIT || k == .SEQ_NTH

/-- The kinds of the extended functions (`ExtfSolver`'s function kinds). -/
def extfKind (k : Kind) : Bool :=
  k == .STRING_SUBSTR || k == .STRING_UPDATE || k == .STRING_INDEXOF || k == .STRING_INDEXOF_RE ||
    k == .STRING_ITOS || k == .STRING_STOI || k == .STRING_REPLACE || k == .STRING_REPLACE_ALL ||
    k == .STRING_REPLACE_RE || k == .STRING_REPLACE_RE_ALL || k == .STRING_CONTAINS ||
    k == .STRING_IN_REGEXP || k == .STRING_LEQ || k == .STRING_TO_CODE || k == .STRING_TO_LOWER ||
    k == .STRING_TO_UPPER || k == .STRING_REV || k == .SEQ_UNIT || k == .SEQ_NTH

/-- The kinds whose applications to constants the engine evaluates. -/
def interpretedKind (k : Kind) : Bool := congruenceKind k && k != .SEQ_NTH

/-! ## Facts -/

/-- `notifyFact`: a pending conflict is sent (`processConflict`; the
minimization of a prefix conflict needs regular expressions). -/
def processPendingConflict : EEM Unit := do
  if (← get).teConflict then return
  let some (id, premises) := (← st).pendingConflict | return
  let mut exp : Array Node := #[]
  for p in premises do
    for a in ← explainLit p do
      exp := flattenAnd a exp
  let conf := EE.mkAnd exp
  modifyStrings fun s => { s with conflict := some (id, conf, premises) }
  note (.conflict stringsTheory id conf)
  modify fun s => { s with teConflict := true }

/-- `preNotifyFact` and `Theory::check`'s processing of one fact: a
disequality of strings is recorded, the fact asserted to the engine. -/
def assertFact (fact : Node) : EEM Unit := do
  let (atom, pol) := match fact with
    | .app (.kind .NOT) #[a] => (a, false)
    | _ => (fact, true)
  if let .app (.kind .EQUAL) #[a, b] := atom then
    if !pol && isStringLike a then
      modifyStrings fun s => { s with disequalities := s.disequalities.push (Node.eqNode a b) }
  match atom with
  | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol fact
  | _ => let _ ← assertPredicate atom pol fact
  -- `EagerSolver::notifyFact`: the constant endpoints of a positive membership
  -- in a concatenation (`stringsEagerLenEntRegexp` is off)
  if let .app (.kind .STRING_IN_REGEXP) #[x, r] := atom then
    if pol && r.getKind == .REGEXP_CONCAT && !(← st).pendingConflict.isSome then
      let _ ← addEndpointsToEqcInfo atom r (← rep x)
  processPendingConflict

/-! ## Registration (`TermRegistry`) -/

/-- What registration needs from the theory engine. -/
structure Ops (m : Type → Type) where
  /-- Run an operation of the equality engine, process its notes, and register
  the atoms of the lemmas sent (`TheoryEngine::lemma`). -/
  run : {α : Type} → EEM α → m α
  /-- `preferPhase`. -/
  phase : Node → Bool → m Unit
  /-- `Valuation::hasSatValue`. -/
  hasSatValue : Node → m Bool

section
variable {m : Type → Type} [Monad m] (ops : Ops m)

/-- `registerTermAtomic`: the split of the length of an atomic term
(`STRINGS_REGISTER_TERM_ATOMIC`, `lengthPositive`), with its phases. -/
def registerTermAtomic (n : Node) (s : LengthStatus) : m Unit := do
  if (← ops.run st).lengthLemmaTerms.contains ⟨n⟩ then return
  ops.run (modifyStrings fun st => { st with lengthLemmaTerms := st.lengthLemmaTerms.insert ⟨n⟩ })
  if s == .ignore || n.isConst then return
  let len := mkLen n
  if s == .geqOne then
    let lem := Node.mkNode .AND #[Node.notNode (Node.eqNode n (emptyOf n)), Node.mkNode .GT #[len, intConst 0]]
    let _ ← ops.run (trustedLemma lem "STRINGS_REGISTER_TERM_ATOMIC")
    return
  if s == .one then
    let _ ← ops.run (trustedLemma (Node.eqNode len (intConst 1)) "STRINGS_REGISTER_TERM_ATOMIC")
    return
  let lenZ := Node.eqNode len (intConst 0)
  let emp := Node.eqNode n (emptyOf n)
  let lem := Node.mkNode .OR #[Node.mkNode .AND #[lenZ, emp], Node.mkNode .GT #[len, intConst 0]]
  let caseEmpty ← ops.run (rw (Node.mkNode .AND #[lenZ, emp]))
  -- the preferred phases, in the order of node ids (`std::map`)
  let phases ← if caseEmpty.isConst then pure [] else do
    let a ← ops.run (rw lenZ)
    let b ← ops.run (rw emp)
    let older ← ops.run (do return ageLt (← get).nodeIds b a (← read).declOrder (← read).order)
    pure (if older then [b, a] else [a, b])
  let _ ← ops.run (trustedLemma lem "STRINGS_REGISTER_TERM_ATOMIC")
  for p in phases do ops.phase p true

/-- `getRegisterTermLemma`: for a constant or a concatenation, the proxy
variable `k` (the purification skolem of the term) with `(= k n)` and its
length; for another term whose length does not rewrite, the split of its
length (and no lemma). -/
def registerTermLemma (n : Node) : m (Option Node) := do
  let isConcat := n.getKind == .STRING_CONCAT
  if !isConcat && !n.isConst then
    let l := mkLen n
    if (← ops.run (rw l)) == l then
      registerTermAtomic ops n .split
      return none
  let sk := Node.skolem .PURIFY #[n]
  let eq ← ops.run (rw (Node.eqNode sk n))
  ops.run (modifyStrings fun s => { s with proxyVar := s.proxyVar.insert ⟨n⟩ sk })
  if n.isConst || isConcat then registerTermAtomic ops sk .ignore
  let skl := mkLen sk
  let lsum ← match n with
    | .app (.kind .STRING_CONCAT) cs => do
      let s ← ops.run st
      let ls := cs.map fun c => (s.proxyVarToLength.get? ⟨c⟩).getD (mkLen c)
      ops.run (rw (Node.mkNode .ADD ls))
    | .const (.string w) => pure (intConst w.length)
    | _ => ops.run (rw (mkLen n))
  ops.run (modifyStrings fun s => { s with proxyVarToLength := s.proxyVarToLength.insert ⟨sk⟩ lsum })
  let ceq ← ops.run (rw (Node.eqNode skl lsum))
  return some (Node.mkNode .AND #[eq, ceq])

/-- `utils::eagerReduce`, for the terms other than strings
(`STRING_EAGER_REDUCTION`): the range of a code, the bounds of an index and of
an integer of a string. (`str.contains` is not reduced eagerly; `seq.nth`
comes with sequences.) -/
def eagerReduce (t : Node) : Option Node :=
  let negOne := intConst (-1)
  match t with
  | .app (.kind .STRING_TO_CODE) #[s] =>
    let codeLen := Node.eqNode (mkLen s) (intConst 1)
    let range := Node.mkNode .AND #[Node.mkNode .GEQ #[t, intConst 0], Node.mkNode .LT #[t, intConst 196608]]
    some (Node.mkNode .ITE #[codeLen, range, Node.eqNode t negOne])
  | .app (.kind .STRING_INDEXOF) #[x, _, n] | .app (.kind .STRING_INDEXOF_RE) #[x, _, n] =>
    some (Node.mkNode .AND #[Node.mkNode .OR #[Node.eqNode t negOne, Node.mkNode .GEQ #[t, n]],
      Node.mkNode .LEQ #[t, mkLen x]])
  | .app (.kind .STRING_STOI) _ => some (Node.mkNode .GEQ #[t, negOne])
  | _ => none

/-- `registerTerm`: the length lemma of a string term, or the eager reduction
of another (but the code of a constant), once (user context). -/
def registerTerm (n : Node) : m Unit := do
  if (← ops.run st).registered.contains ⟨n⟩ then return
  ops.run (modifyStrings fun s => { s with registered := s.registered.insert ⟨n⟩ })
  if isStringLike n then
    if let some lem ← registerTermLemma ops n then
      let _ ← ops.run (trustedLemma lem "STRINGS_REGISTER_TERM")
  else
    let doEager := match n with
      | .app (.kind .STRING_TO_CODE) #[a] => !(originalForm a).isConst
      | .app (.kind .STRING_CONTAINS) _ => false
      | _ => true
    if doEager then
      if let some lem := eagerReduce n then
        let _ ← ops.run (trustedLemma lem "STRINGS_REGISTER_TERM")

mutual
  /-- `registerType`: the empty word of a string type is preregistered and
  registered. -/
  partial def registerType (T : TypeNode) : m Unit := do
    if (← ops.run st).registeredTypes.contains T then return
    ops.run (modifyStrings fun s => { s with registeredTypes := s.registeredTypes.push T })
    match T with
    | .string =>
      preRegisterTerm emptyWord
      registerTerm ops emptyWord
    | .sequence E =>
      let e : Node := .const (.emptySeq E)
      preRegisterTerm e
      registerTerm ops e
    | _ => pure ()

  /-- `preRegisterTerm`: registered (eagerly), its type registered, then added
  to the equality engine (an equality as a trigger predicate). -/
  partial def preRegisterTerm (n : Node) : m Unit := do
    if (← ops.run st).preregistered.contains ⟨n⟩ then return
    ops.run (modifyStrings fun s => s.addPrereg n)
    match n with
    | .app (.kind .STRING_IN_REGEXP) _ => ops.phase n true
    | .app (.kind .STRING_TO_CODE) _ => ops.run (modifyStrings fun s => { s with hasStrCode := true })
    | _ => pure ()
    registerTerm ops n
    if let some T := n.typeHint then registerType T
    -- a predicate is a trigger unless it has a SAT value
    -- (`addEqualityEngineTriggerPredicate`)
    -- (another predicate is not added: it is when it is asserted)
    match n with
    | .app (.kind k) _ =>
      if k == .EQUAL || k == .STRING_CONTAINS || k == .STRING_LEQ ||
          (k == .SEQ_NTH && n.typeHint == some .boolean) then
        if ← ops.hasSatValue n then ops.run (addTerm n) else ops.run (UF.addTriggerPredicate n)
      else if n.typeHint != some .boolean then ops.run (addTerm n)
    | _ => ops.run (addTerm n)
    -- the function terms, for the care graph
    match n with
    | .app (.kind k) _ =>
      if congruenceKind k && k != .STRING_CONCAT && k != .STRING_IN_REGEXP then
        ops.run (modifyStrings fun s => { s with functionTerms := s.functionTerms.push n })
    | _ => pure ()
    -- `ExtTheory::registerTerm`
    if extfKind n.getKind then ops.run (modifyStrings fun s => s.registerExt n)
end

end

end Telos.Solver.Strings
