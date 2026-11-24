import Telos.Rewriter.Rewrite
import Telos.Solver.Theory.QuantEMatching
import Telos.Solver.Event

/-!
# The quantifiers engine

A port of cvc5's `QuantifiersEngine` (`src/theory/quantifiers_engine.cpp`) and
`TheoryQuantifiers`, with the modules of conflict-based instantiation and
E-matching (`QuantEMatching.lean`) (`docs/theory-engine-plan.md`, Stage 10):
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

Instantiation is `QuantInst.lean`.
-/

namespace Telos.Solver.Quant

/-- `registerQuantifierInternal`: the conflict-based instantiation's
information of `q`. -/
def registerQuantifier (q : Node) : EM Unit := do
  if (← get).st.registered.contains ⟨q⟩ then return
  modify fun e => { e with st := { e.st with registered := e.st.registered.insert ⟨q⟩ } }
  let ((qi, fops), _) ← runM {} (mkQInfo q)
  -- (E-matching's registration: the triggers of the user patterns)
  ematchRegister q
  modify fun e => { e with
    qinfo := e.qinfo.insert ⟨q⟩ qi,
    funcRelDom := fops.foldl (fun m f =>
      let qs := (m.get? ⟨f⟩).getD #[]
      if qs.contains q then m else m.insert ⟨f⟩ (qs.push q)) e.funcRelDom }

/-- `preRegisterQuantifier`. -/
def preRegister (q : Node) : EM Unit := do
  if (← get).st.preregistered.contains ⟨q⟩ then return
  modify fun e => { e with st := { e.st with preregistered := e.st.preregistered.insert ⟨q⟩ } }
  if ← reduceQuantifier q then return
  registerQuantifier q

/-- The skolems of `q` (`getSkolemConstants`). -/
def skolemsOf (q : Node) : Array Node :=
  (quantVars q).mapIdx fun i _ => Node.skolem .QUANTIFIERS_SKOLEMIZE #[q, .const (.integer i)]

/-- `assertQuantifier`: a negated formula is skolemized once (user context); an
asserted one registered and recorded. -/
def assertQuantifier (q : Node) (pol : Bool) : EM Unit := do
  if ← reduceQuantifier q then return
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

/-! ## Bounded quantified formulas

The formulas the reductions of strings make (`isBoundedForall`), over integers
bounded by literals of their bodies: cvc5's `BoundedIntegers`, `checkOwnership`
(integer ranges only), and its model engine (`FullModelChecker`) with them:
at last call, an instance that the model does not make true, the first in the
order of the values. The decision strategy of the ranges
(`IntRangeDecisionHeuristic`) is not ported. -/

/-- The bounds of the variable `v` by the disjunct `d` of a body, whose
negation is assumed: a lower (`true`) or an upper bound. -/
def boundOfDisjunct (v d : Node) : Array (Bool × Node) :=
  let (atom, pol) := match d with
    | .app (.kind .NOT) #[a] => (a, true)
    | a => (a, false)
  match atom with
  | .app (.kind .GEQ) #[a, b] =>
    if a.typeHint != some .integer then #[] else
    -- `p ≥ 0` (`pol`), or `p ≤ -1`
    let p := Telos.Arith.polyOf (Node.mkNode .SUB #[a, b])
    let c := (p.find? (·.1 == [v])).map (·.2)
    let rest := p.filter (·.1 != [v])
    if rest.any (·.1.contains v) then #[] else
    match c with
    | some c =>
      if c == 1 then
        let r := Telos.Arith.Poly.scale rest (-1)
        if pol then #[(true, r.toNode false)]
        else #[(false, (Telos.Arith.Poly.add r (Telos.Arith.Poly.const (-1))).toNode false)]
      else if c == -1 then
        if pol then #[(false, (Telos.Arith.Poly.scale rest 1).toNode false)]
        else #[(true, (Telos.Arith.Poly.add rest (Telos.Arith.Poly.const 1)).toNode false)]
      else #[]
    | none => #[]
  | _ => #[]

/-- The variables of `q` in the order they are found bounded, each with its
bounds; none if one is not. -/
def boundsOf (q : Node) : Option (Array (Node × Node × Node)) := Id.run do
  let vs := quantVars q
  let ds := match quantBody q with
    | .app (.kind .OR) cs => cs
    | b => #[b]
  let mut out : Array (Node × Node × Node) := #[]
  for _ in vs do
    for v in vs do
      if out.any (·.1 == v) then continue
      let bs := ds.flatMap (boundOfDisjunct v)
      let ok (t : Node) : Bool := t.vars.all fun x => !vs.contains x || out.any (·.1 == x)
      -- (a later literal's bound replaces an earlier one's)
      let lo := (bs.filter fun (l, t) => l && ok t).back?
      let hi := (bs.filter fun (l, t) => !l && ok t).back?
      match lo, hi with
      | some (_, l), some (_, h) => out := out.push (v, l, h)
      | _, _ => pure ()
  return if out.size == vs.size then some out else none

/-- The most values of a variable that are enumerated. -/
def rangeLimit : Int := 100000

/-- `FullModelChecker::exhaustiveInstantiate` of a bounded formula: the number
of instances added (at most one), and whether all were considered. -/
partial def exhaustiveInstantiate (rd : Round) (q : Node) : EM (Nat × Bool × Round) := do
  let some bs := boundsOf q | return (0, false, rd)
  let c ← ectx
  let vs := quantVars q
  let rec go (rd : Round) (i : Nat) (asg : Array (Node × Node)) : EM (Nat × Bool × Round) := do
    let subst (t : Node) : Node := substitute (asg.map (·.1)) (asg.map (·.2)) t
    if h : i < bs.size then
      let (v, l, u) := bs[i]
      let some lv := c.modelInt (subst l) | return (0, false, rd)
      let some uv := c.modelInt (subst u) | return (0, false, rd)
      if uv - lv > rangeLimit then return (0, false, rd)
      let mut rd := rd
      let mut complete := true
      for j in [0:(uv - lv + 1).toNat] do
        let k := Node.const (.integer (lv + (j : Int)))
        let (n, ok, rd') ← go rd (i + 1) (asg.push (v, k))
        rd := rd'
        complete := complete && ok
        if n > 0 then return (n, complete, rd)
      return (0, complete, rd)
    else
      let terms := vs.map fun v => ((asg.find? (·.1 == v)).map (·.2)).getD v
      if c.modelBool (substitute vs terms (quantBody q)) == some true then return (0, true, rd)
      let (ok, rd) ← addInstantiation rd q terms "QUANTIFIERS_INST_FMF_FMC_EXH"
      return (if ok then 1 else 0, true, rd)
  go rd 0 #[]

/-- `ModelEngine::check`: the bounded formulas, in the order of relevance;
whether every asserted formula is one of them, completely instantiated. -/
def modelEngineCheck (rd : Round) : EM (Bool × Round) := do
  let mut rd := rd
  let mut complete := true
  for q in ← orderedAsserted do
    if !q.isBoundedForall then
      complete := false
      continue
    let (_, ok, rd') ← exhaustiveInstantiate rd q
    rd := rd'
    if !ok then complete := false
  return (complete, rd)

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
  -- E-matching (`getInstWhenNeedsCheck`, `inst-when=full-last-call`, with
  -- `d_instWhenPhase` 3)
  let emNeeds := anyAsserted && ((e == .full && st.ierCounter % 3 != 0) || e == .lastCall)
  let needs := anyAsserted && (e == .lastCall || qcfNeeds || emNeeds)
  if needs then
    -- the utilities' reset (the term database, at full effort and last call)
    let (_, rd) ← runM {} (if e != .standard then resetTermDb else pure ())
    let mut rd := rd
    -- the modules' `reset_round` (at the standard effort, those that need a
    -- check)
    if e != .standard || emNeeds then rd ← ematchResetRound rd
    -- the modules' efforts: conflict, standard, model, last call
    let lemmasBefore := (← getThe Out).lemmas.size
    for qe in [0, 1, 2, 3] do
      if qe == 0 && qcfNeeds then rd ← qcfCheck rd
      if qe == 1 && emNeeds && !rd.inConflict then rd ← ematchCheck rd (e == .lastCall)
      let mut complete := false
      if qe == 2 && e == .lastCall then
        let (ok, rd') ← modelEngineCheck rd
        rd := rd'
        complete := ok
      for l in rd.pending do let _ ← emitLemma l
      rd := { rd with pending := #[] }
      if (← getThe Out).lemmas.size > lemmasBefore || rd.inConflict then break
      if qe == 0 then
        -- `incrementInstRoundCounters`
        if e == .full then
          let st := (← get).st
          if st.ierCounterLastLc != st.ierCounterLc || st.ierCounter % 3 != 0 then
            modify fun en => { en with st := { en.st with ierCounter := en.st.ierCounter + 1,
                                                          ierCounterLastLc := en.st.ierCounterLc } }
        else if e == .lastCall then
          modify fun en => { en with st := { en.st with ierCounterLc := en.st.ierCounterLc + 1 } }
      else if qe == 2 && e == .lastCall then
        -- no module is complete for an asserted formula, but for the bounded
        unsound := !complete
        break
  else
    if e == .full then
      let st := (← get).st
      if st.ierCounterLastLc != st.ierCounterLc || st.ierCounter % 3 != 0 then
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
