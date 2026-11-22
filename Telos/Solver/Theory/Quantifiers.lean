import Telos.Solver.Theory.QuantConflictFind
import Telos.Solver.Event

/-!
# The quantifiers engine

A port of cvc5's `QuantifiersEngine` (`src/theory/quantifiers_engine.cpp`) and
`TheoryQuantifiers`, with the conflict-based instantiation module only
(`docs/theory-engine-plan.md`, Stage 10, step 1):
- a quantified formula is registered when preregistered or asserted
  (`registerQuantifierInternal`: the information of conflict-based
  instantiation, `QInfo`);
- an asserted negated one is skolemized (`QUANTIFIERS_SKOLEMIZE`,
  `(=> (not q) (not body[k]))` for the skolems `(@quantifiers_skolemize q i)`);
- an asserted one is recorded (`FirstOrderModel::assertQuantifier`);
- `check` at standard, full and last-call effort: the round's reset (the term
  database, the classes by type), then the modules, at each of their efforts
  (`QEFFORT_CONFLICT`, ...), and at last call, the completeness check: no
  module is complete for a quantified formula, so the model is unsound
  (`QUANTIFIERS`), unless the term database's relevant terms grow
  (`shouldRecheck`, `term-db-mode=relevant-all-delay`), in which case another
  check is asked for.

Instantiations (`Instantiate::addInstantiation`) are skipped when the instance
is entailed (`inst-no-entail`) or recorded, and the lemma `(=> q body)` is
rewritten and sent once (the inference manager's cache).
-/

namespace Telos.Solver.Quant

/-- The quantifiers engine's state. -/
structure Eng where
  st : State := {}
  /-- The information of each registered formula (`d_qinfo`, user context). -/
  qinfo : Std.HashMap Key QInfo := {}
  /-- `d_func_rel_dom`: the formulas whose propagating variables have each
  operator. -/
  funcRelDom : Std.HashMap Key (Array Node) := {}
  deriving Inhabited

/-- What a call of the engine gives back. -/
structure Out where
  lemmas : Array Lemma := #[]
  /-- The skolems created, in order. -/
  skolems : Array Node := #[]
  /-- The model is unsound (`setModelUnsound`, `QUANTIFIERS`). -/
  modelUnsound : Bool := false
  /-- Another check is asked for (`markUsed`). -/
  markUsed : Bool := false
  deriving Inhabited

abbrev EM := StateT Eng (StateT Out (ReaderT Ctx Id))

/-- Run an operation of the term database and the round's data. -/
def runM (rd : Round) (x : M α) : EM (α × Round) := do
  let c ← (read : ReaderT Ctx Id Ctx)
  let e ← get
  let (a, s) := (x.run c).run { st := e.st, rd }
  set { e with st := s.st }
  return (a, s.rd)

def emitLemma (l : Lemma) : EM Bool := do
  let e ← get
  if e.st.lemmaCache.contains ⟨l.lem⟩ then return false
  set { e with st := { e.st with lemmaCache := e.st.lemmaCache.insert ⟨l.lem⟩ } }
  modifyThe Out fun o => { o with lemmas := o.lemmas.push l }
  return true

/-- `registerQuantifierInternal`: the conflict-based instantiation's
information of `q`. -/
def registerQuantifier (q : Node) : EM Unit := do
  if (← get).st.registered.contains ⟨q⟩ then return
  modify fun e => { e with st := { e.st with registered := e.st.registered.insert ⟨q⟩ } }
  let ((qi, fops), _) ← runM {} (mkQInfo q)
  modify fun e => { e with
    qinfo := e.qinfo.insert ⟨q⟩ qi,
    funcRelDom := fops.foldl (fun m f =>
      let qs := (m.get? ⟨f⟩).getD #[]
      if qs.contains q then m else m.insert ⟨f⟩ (qs.push q)) e.funcRelDom }

/-- `preRegisterQuantifier`. -/
def preRegister (q : Node) : EM Unit := do
  if (← get).st.preregistered.contains ⟨q⟩ then return
  modify fun e => { e with st := { e.st with preregistered := e.st.preregistered.insert ⟨q⟩ } }
  registerQuantifier q

/-- The skolems of `q` (`getSkolemConstants`). -/
def skolemsOf (q : Node) : Array Node :=
  (quantVars q).mapIdx fun i _ => Node.skolem .QUANTIFIERS_SKOLEMIZE #[q, .const (.integer i)]

/-- `assertQuantifier`: a negated formula is skolemized once (user context); an
asserted one registered and recorded. -/
def assertQuantifier (q : Node) (pol : Bool) : EM Unit := do
  if !pol then
    if (← get).st.skolemized.contains ⟨q⟩ then return
    modify fun e => { e with st := { e.st with skolemized := e.st.skolemized.insert ⟨q⟩ } }
    let ks := skolemsOf q
    modifyThe Out fun o => { o with skolems := o.skolems ++ ks }
    let body := substitute (quantVars q) ks (quantBody q)
    let lem := Node.mkNode .IMPLIES #[Node.notNode q, Node.notNode body]
    let _ ← emitLemma { id := "QUANTIFIERS_SKOLEMIZE", lem, skolemize := some q }
    return
  registerQuantifier q
  modify fun e => { e with st := { (e.st.log .asserted) with asserted := e.st.asserted.push q } }

/-- `Instantiate::addInstantiation`: false if the instance is entailed, recorded,
or its lemma was sent. -/
def addInstantiation (rd : Round) (q : Node) (terms : Array Node) (id : String) : EM (Bool × Round) := do
  let vs := quantVars q
  let subs : Subs := (vs.zip terms).foldl (fun m (v, t) => m.insert ⟨v⟩ t) {}
  let (ent, rd) ← runM rd (isEntailed (quantBody q) subs false true)
  if ent then return (false, rd)
  let key : Key := ⟨Node.mkNode .AND (#[q] ++ terms)⟩
  if (← get).st.insts.contains key then return (false, rd)
  modify fun e => { e with st := { e.st with insts := e.st.insts.insert key } }
  let body := substitute vs terms (quantBody q)
  let c ← (read : ReaderT Ctx Id Ctx)
  let lem₀ := Node.mkNode .IMPLIES #[q, body]
  let lem := c.rewrite lem₀
  return (← emitLemma { id, lem, inst := some (q, terms, lem₀) }, rd)

/-- `FirstOrderModel::markRelevant`. -/
def markRelevant (q : Node) : EM Unit :=
  modify fun e =>
    if e.st.lastRlv == some q then e else
    { e with st := { e.st with rlvVec := (e.st.rlvVec.filter (· != q)).push q, lastRlv := some q } }

/-- The asserted formulas in the order of relevance (`reset_round`). -/
def orderedAsserted : EM (Array Node) := do
  let st := (← get).st
  if st.rlvVec.isEmpty then return st.asserted
  let mut rest := st.asserted
  let mut out := #[]
  for i in [0:st.rlvVec.size] do
    let q := st.rlvVec[st.rlvVec.size - 1 - i]!
    if rest.contains q then
      out := out.push q
      rest := rest.erase q
  return out ++ st.asserted.filter fun q => !out.contains q

/-! ## Conflict-based instantiation -/

/-- `checkQuantifiedFormula`: the instances found, at the effort, added; whether
one was (for the conflict effort, it stops the round). -/
def checkQuantifiedFormula (rd : Round) (q : Node) (eqcs : Std.HashMap (Option TypeNode) (Array Node))
    (conflictEffort : Bool) : EM (Nat × Round × Array Node) := do
  let some qi := (← get).qinfo.get? ⟨q⟩ | return (0, rd, #[])
  if !qi.valid then return (0, rd, #[])
  let nv := qi.numVars
  let d0 : QDyn := { match_ := Array.replicate nv none, matchTerm := Array.replicate nv none,
                     instMatch := Array.replicate qi.nvars none,
                     mg := Array.replicate qi.mgs.size {} }
  let env : QEnv := { qi, eqcs, conflictEffort }
  -- `QuantInfo::reset_round`
  let resetRound : QM Bool := do
    if !(← mgResetRound qi.root) then return false
    for (_, g) in qi.varMg do
      if !(← mgResetRound g) then return false
    mgReset qi.root false
    return true
  let ((ok, qs), rd) ← runM rd ((resetRound.run env).run { d := d0 })
  if !ok then return (0, rd, qs.irrFunc)
  let mut qs := qs
  let mut rd := rd
  let mut added := 0
  repeat
    let ((next, qs'), rd') ← runM rd (((getNextMatch qi.root).run env).run qs)
    qs := qs'
    rd := rd'
    if !next then break
    let ((spur, qs'), rd') ← runM rd ((isMatchSpurious.run env).run qs)
    qs := qs'
    rd := rd'
    if spur then continue
    let (((complete, assigned), qs'), rd') ← runM rd (((completeMatch #[]).run env).run qs)
    qs := qs'
    rd := rd'
    if !complete then continue
    let ((terms, qs'), rd') ← runM rd ((getMatch.run env).run qs)
    qs := qs'
    rd := rd'
    let ((tcs, qs'), rd') ← runM rd (((isTConstraintSpurious terms).run env).run qs)
    qs := qs'
    rd := rd'
    if !tcs then
      let id := if conflictEffort then "QUANTIFIERS_INST_CBQI_CONFLICT" else "QUANTIFIERS_INST_CBQI_PROP"
      let (ok, rd') ← addInstantiation rd q terms id
      rd := rd'
      if !ok then return (added, rd, qs.irrFunc)
      added := added + 1
      if conflictEffort then
        markRelevant q
        modify fun e => { e with st := { (e.st.log .conflictInst) with conflictInst := true } }
        return (added, rd, qs.irrFunc)
      else markRelevant q
    let ((_, qs'), rd') ← runM rd (((revertMatch assigned).run env).run qs)
    qs := qs'
    rd := rd'
  return (added, rd, qs.irrFunc)

/-- `QuantConflictFind::check` at the conflict effort of the modules: the
asserted formulas, at the conflict effort, then at that of propagations. -/
def qcfCheck (rd : Round) : EM Round := do
  if (← get).st.conflictInst then return rd
  let c ← (read : ReaderT Ctx Id Ctx)
  -- `reset_round`: the classes, by type, of the relevant terms
  let (hasTerms, rd) ← runM rd (c.reps.mapM hasTermCurrent)
  let mut eqcs : Std.HashMap (Option TypeNode) (Array Node) := {}
  for (r, h) in c.reps.zip hasTerms do
    if h then eqcs := eqcs.alter r.typeHint fun l => some ((l.getD #[]).push r)
  let mut rd := rd
  let quants ← orderedAsserted
  for conflictEffort in [true, false] do
    let mut irrQuant : Std.HashSet Key := {}
    let mut added := 0
    for q in quants do
      if irrQuant.contains ⟨q⟩ then continue
      let (a, rd', irr) ← checkQuantifiedFormula rd q eqcs conflictEffort
      rd := rd'
      added := added + a
      for f in irr do
        for q' in ((← get).funcRelDom.get? ⟨f⟩).getD #[] do irrQuant := irrQuant.insert ⟨q'⟩
      if (← get).st.conflictInst || rd.inConflict then break
    if added > 0 || rd.inConflict then break
  return rd

/-! ## The check -/

/-- `QuantifiersEngine::check`, at the effort `e`; `needCheck` is the theory
engine's (`Valuation::needCheck`), `allTerms` the terms of the equality
engine (for `shouldRecheck`). -/
def check (e : Effort) (needCheck : Bool) (allTerms : Array Node) : EM Unit := do
  let st := (← get).st
  let mut unsound := false
  let anyAsserted := !st.asserted.isEmpty
  -- the modules that need a check: conflict-based instantiation, at full effort
  let qcfNeeds := anyAsserted && !st.conflictInst && e == .full
  let needs := anyAsserted && (e == .lastCall || qcfNeeds)
  if needs then
    -- the utilities' reset (the term database, at full effort and last call)
    let (_, rd) ← runM {} (if e != .standard then resetTermDb else pure ())
    let mut rd := rd
    -- the modules' efforts: conflict, standard, model, last call
    let lemmasBefore := (← getThe Out).lemmas.size
    for qe in [0, 1, 2, 3] do
      if qe == 0 && qcfNeeds then rd ← qcfCheck rd
      for l in rd.pending do let _ ← emitLemma l
      rd := { rd with pending := #[] }
      if (← getThe Out).lemmas.size > lemmasBefore || rd.inConflict then break
      if qe == 0 then
        -- `incrementInstRoundCounters`
        if e == .full then
          let st := (← get).st
          if st.ierCounterLastLc != st.ierCounterLc || st.ierCounter % 2 != 0 then
            modify fun en => { en with st := { en.st with ierCounter := en.st.ierCounter + 1,
                                                          ierCounterLastLc := en.st.ierCounterLc } }
        else if e == .lastCall then
          modify fun en => { en with st := { en.st with ierCounterLc := en.st.ierCounterLc + 1 } }
      else if qe == 2 && e == .lastCall then
        -- no module is complete for an asserted formula
        unsound := true
        break
  else
    if e == .full then
      let st := (← get).st
      if st.ierCounterLastLc != st.ierCounterLc || st.ierCounter % 2 != 0 then
        modify fun en => { en with st := { en.st with ierCounter := en.st.ierCounter + 1,
                                                      ierCounterLastLc := en.st.ierCounterLc } }
    else if e == .lastCall then
      modify fun en => { en with st := { en.st with ierCounterLc := en.st.ierCounterLc + 1 } }
  if e == .lastCall && !needCheck && (← getThe Out).lemmas.isEmpty then
    if unsound then
      -- `shouldRecheck`: the terms of the engine not relevant yet become so
      let (hs, _) ← runM {} (allTerms.mapM hasTermCurrent)
      let recheck := hs.any (!·)
      if recheck then
        let _ ← runM {} (do for t in allTerms do setHasTerm t)
        modifyThe Out fun o => { o with markUsed := true }
      else modifyThe Out fun o => { o with modelUnsound := true }

end Telos.Solver.Quant
