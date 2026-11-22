import Telos.Solver.Engine
import Telos.Solver.Cnf
import Telos.Solver.Sat.Minisat

/-!
# The prop engine: the SAT solver and the theory engine

A port of cvc5's `PropEngine` and `TheoryProxy` (`src/prop/prop_engine.cpp`,
`src/prop/theory_proxy.cpp`), with MiniSat (`Telos/Solver/Sat/Minisat.lean`)
as the SAT solver and the CNF stream (`Telos/Solver/Cnf.lean`) between the two:
- the input formulas are translated by the CNF stream; their atoms get SAT
  literals and are preregistered (eagerly, `TheoryPreregistrar`), and again
  after a backtrack above the level they were preregistered at;
- the literals the SAT solver assigns are queued, and asserted to the theory
  engine at its next check (`theoryCheck`), whose propagations the SAT solver
  takes (`theoryPropagate`), and explains when it needs to
  (`explainPropagation`);
- the theories' lemmas, and their conflicts (negated, explained by literals of
  the SAT solver), go through the CNF stream to the SAT solver, which queues
  them, as it is busy;
- the SAT solver's decision levels are context levels of the engine, above
  the level of `check-sat` (1), at which the input is asserted.

The decisions are MiniSat's own (`--decision=internal`, cvc5's default for
QF_UF and QF_UFDT): no theory asks for one, and there is no decision engine.

`TheoryProxy` is all the SAT solver sees of the rest, and `Cnf.SatOp` all the
CNF stream asks of the SAT solver: that is where another CDCL(T) solver goes
(`docs/theory-engine-plan.md`, Stage 6).
-/

namespace Telos.Solver

open Telos.Sat

/-! ## The engine's side -/

/-- `TheoryProxy::enqueueTheoryLiteral`: the SAT solver assigned a theory
literal; it is asserted at the next check. The engine's view of the SAT
assignment has it at once (`PropEngine::hasValue`). -/
def enqueueSat (lit : Node) : EngineM Unit := do
  let (atom, pol) := atomOf lit
  modify fun s => { s with assignment := s.assignment.insert ⟨atom⟩ pol,
                           assignTrail := s.assignTrail.push ⟨atom⟩,
                           satQueue := s.satQueue.push lit }

/-- `TheoryProxy::theoryCheck`: the queued literals are asserted, then the
theories are checked. -/
def satCheck (e : Effort) : EngineM Unit := do
  let q ← modifyGet fun s => (s.satQueue, { s with satQueue := #[], activatedSkDefs := false })
  let mut e := e
  for lit in q do
    modify fun s => { s with asserted := s.asserted.push lit }
    assertFact lit
    -- `TheoryProxy::theoryCheck`: the skolem definitions the literal activates
    -- go to the decision engine, and a full check becomes a standard one
    if (← read).decision != .internal then
      let defs ← activateSkolems lit
      if !defs.isEmpty then
        modify fun s => { s with decisionLocalQueue := s.decisionLocalQueue ++ defs, activatedSkDefs := true }
        if e == .full then e := .standard
  flushLemmas
  check e
  flushLemmas

/-- Where a clause given to the SAT solver comes from. -/
inductive BaseTag where
  /-- The CNF stream. -/
  | cnf (tag : Cnf.ClauseTag)
  /-- An explanation of a theory propagation, with its certificate. -/
  | theory (cert : Option SatProof.Just)
  /-- A clause that follows by unit propagation from these clauses, with their
  certificates (`stepClauses`). -/
  | derived (aux : Array (Array Node × Option SatProof.Just))
  deriving Inhabited

/-- The explanation of a propagated literal: the verified explanation
(`EE.explainLitV`), or else the equality engine's; and the certificate of the
clause it makes (the literal, or the negation of a reason), which refutes the
reasons with the literal's negation. -/
def satExplainQuiet (lit : Node) : EngineM (Array Node × BaseTag) := do
  let c ← read
  -- (the theory that propagated it explains it)
  let byArith := match (← get).propagator.get? ⟨lit⟩ with
    | some T => T == .THEORY_ARITH
    | none => c.theoryOf (atomOf lit).1 == .THEORY_ARITH
  if c.arithSolver && byArith then
    -- the linear solver's explanation, and its certificate
    let (exp, steps) ← explainAllSteps #[lit] false true
    let cert ← withArith (Arith.explainCert lit)
    if steps.isEmpty then return (exp, .theory (cert.map (.arith (exp.push (negate lit)) ·)))
    -- the certificate is over the linear solver's own explanation, which the
    -- steps give from the literals of the clause
    let e₀ ← withArith (Arith.explain lit)
    let main := ((e₀.map negate).push lit, cert.map (.arith (e₀.push (negate lit)) ·))
    return (exp, .derived (#[main] ++ (← stepClauses exp steps)))
  -- (the verified explanation, if its literals are all the SAT solver's: one
  -- that another theory propagated, such as a shared equality of arithmetic,
  -- is explained in turn)
  let asg := (← get).assignment
  let fromSat (l : Node) : Bool := let (a, p) := atomOf l; asg.get? ⟨a⟩ == some p
  let (exp, steps) ← match (EE.explainLitV (← exCtx) lit).filter (·.all fromSat) with
    | some exp => pure (exp, #[])
    | none =>
      modify fun s => { s with unverifiedExplains := s.unverifiedExplains + 1 }
      if !c.eeSolver then pure (#[], #[]) else explainAllSteps #[lit] false true
  let s ← get
  -- (from the literals of the clause only, and those the linear solver
  -- explained)
  let ariths := steps.filter (·.arith)
  let lits := exp ++ ariths.map (·.lit)
  let r := EE.conflictOfPropagation s.ee (lits.push (negate lit)) lits lit (negate lit)
  let cert := r.toOption.map
    fun (A, q) => SatProof.Just.theory A q
  if ariths.isEmpty then return (exp, .theory cert)
  let main := match cert with
    | some j@(.theory A _) => (A.map negate, some j)
    | _ => ((lits.map negate).push lit, none)
  return (exp, .derived (#[main] ++ (← stepClauses exp ariths)))

/-- `TheoryEngine::getExplanation`, as the SAT solver asks for it. -/
def satExplain (lit : Node) : EngineM (Array Node × BaseTag) := do
  let (exp, cert) ← satExplainQuiet lit
  emit (.explain (← level) lit (EE.mkAnd exp))
  return (exp, cert)

/-! ## The SAT solver's side -/


structure PropState where
  sat : Sat.Solver := {}
  eng : State := {}
  /-- The clauses given to the SAT solver, and those it learned, for the
  certificate of a refutation. -/
  base : Array (Array Lit × BaseTag) := #[]
  learned : Array (Array Lit) := #[]
  /-- The decision engine (`JustificationStrategy`), unless the mode is
  internal. -/
  dec : Decision.State := {}

abbrev PropM := ReaderT Config (StateM PropState)

instance : MonadStateOf Sat.Solver PropM where
  get := do return (← getThe PropState).sat
  set s := modifyThe PropState fun p => { p with sat := s }
  modifyGet f := modifyGetThe PropState fun p =>
    let sat := p.sat
    let p := { p with sat := {} }
    let (a, sat) := f sat
    (a, { p with sat })

/-- Run an operation of the engine; the formulas it gave the decision engine
are added to it (`TheoryProxy::notifyAssertion`). -/
def onEngine (x : EngineM α) : PropM α := do
  let c ← read
  let e ← modifyGetThe PropState fun p => (p.eng, { p with eng := {} })
  let (a, e) := (x.run c).run e
  let q := e.decisionQueue
  let ql := e.decisionLocalQueue
  let e := { e with decisionQueue := #[], decisionLocalQueue := #[] }
  modifyThe PropState fun p =>
    let dec := if c.decision == .internal || q.isEmpty then p.dec else p.dec.addAssertions q
    let dec := if c.decision == .internal || ql.isEmpty then dec else dec.addAssertions ql (isLocal := true)
    { p with eng := e, dec := dec }
  return a

/-- Run an operation of the decision engine, with the SAT solver's values of
the theory atoms. -/
def onDecision (x : Decision.DecM α) : PropM α := do
  let p ← getThe PropState
  let oracle : Decision.Oracle := fun atom =>
    match Cnf.getLiteral? p.eng.cnf atom with
    | some l => match p.sat.value l with
      | .tt => some true
      | .ff => some false
      | _ => none
    | none => none
  let d ← modifyGetThe PropState fun p => (p.dec, { p with dec := {} })
  let (a, d) := (x.run oracle).run d
  modifyThe PropState fun p => { p with dec := d }
  return a

def cnfState : PropM Cnf.State := do return (← getThe PropState).eng.cnf

/-- A failure: the answer will be `unknown`. -/
def satFail (why : String) : PropM Unit :=
  onEngine (modify fun s => { s with satError := s.satError <|> some why })

/-- The SAT literal of a node. -/
def satLit (n : Node) : PropM Lit := do
  match Cnf.getLiteral? (← cnfState) n with
  | some l => return l
  | none =>
    satFail s!"{n.toSmtLibLet {}} has no SAT literal"
    return Cnf.trueLit

/-- The node of a SAT literal. -/
def satNode (l : Lit) : PropM Node := do
  match Cnf.getNode? (← cnfState) l with
  | some n => return n
  | none =>
    satFail s!"the SAT literal {l.x} has no node"
    return Node.mkTrue

/-- Give the CNF stream's requests to the SAT solver, in order, from a
callback of the SAT solver: it is busy, so a clause is queued as a lemma
(`addClause_`), which this does without the SAT solver's callbacks. -/
def flushOps : PropM Unit := do
  let ops ← onEngine (modifyGet fun s =>
    (s.cnf.ops, { s with cnf := { s.cnf with ops := #[] } }))
  for op in ops do
    match op with
    | .newVar isT => modifyThe Sat.Solver fun s => (Sat.Solver.addVar s true true isT).2
    | .phase l => modifyThe Sat.Solver (·.freezePolarity l)
    | .clause lits removable tag =>
      modifyThe PropState fun p => { p with base := p.base.push (lits, .cnf tag) }
      modifyThe Sat.Solver fun s =>
        if !s.ok then s else
        match Sat.Solver.filterClause s lits with
        | none => s
        | some (out, _) =>
          if s.busy then { s with lemmas := s.lemmas.push out, lemmasRemovable := s.lemmasRemovable.push removable }
          else { s with ok := false }

/-- Run an operation of the engine, then give the SAT solver what it asks. -/
def onEngineF (x : EngineM α) : PropM α := do
  let a ← onEngine (do let a ← x; flushLemmas; return a)
  flushOps
  return a

def toEffort : Sat.Effort → Effort
  | .standard => .standard
  | .full => .full

instance : TheoryProxy PropM where
  theoryCheck e := onEngineF (satCheck (toEffort e))
  theoryPropagate := do
    let lits ← onEngine (modifyGet fun s => (s.propagated, { s with propagated := #[] }))
    lits.mapM satLit
  explainPropagation l := do
    let n ← satNode l
    let (exp, tag) ← onEngineF (satExplain n)
    let mut out := #[l]
    for e in (if exp.isEmpty then #[Node.mkTrue] else exp) do out := out.push (← satLit e).neg
    modifyThe PropState fun p => { p with base := p.base.push (out, tag) }
    return out
  enqueueTheoryLiteral l := do
    let n ← satNode l
    onEngine (enqueueSat n)
  contextPush := do
    onEngine pushLevel
    modifyThe PropState fun p => { p with dec := p.dec.push }
  contextPop := do
    onEngine do
      let k := (← get).level - 1
      popTo k
      emit (.pop k)
    modifyThe PropState fun p => { p with dec := p.dec.pop }
  notifyBacktrack := onEngineF satBacktrack
  getNextDecisionRequest := do
    if (← read).decision == .internal then return (Lit.undef, false, false)
    -- (no theory has decision strategies: the decision engine's)
    let (d, stop) ← onDecision Decision.getNext
    match d with
    | some (atom, v) =>
      let l ← satLit atom
      return (if v then l else l.neg, false, stop)
    | none => return (Lit.undef, false, stop)
  isDecisionEngineDone := do
    if (← read).decision == .internal then return false
    onDecision Decision.isDone
  theoryNeedCheck := onEngine do
    let s ← get
    return s.outputUsed || s.lemmasAdded || s.activatedSkDefs
  notifySatClause c := modifyThe PropState fun p => { p with learned := p.learned.push c }
  notifyRestart := pure ()

/-! ## Solving -/

/-- Give the CNF stream's requests to the SAT solver, which is not busy:
`addClause` adds the clauses (and propagates units). -/
def flushOpsTop : PropM Unit := do
  let ops ← onEngine (modifyGet fun s =>
    (s.cnf.ops, { s with cnf := { s.cnf with ops := #[] } }))
  for op in ops do
    match op with
    | .newVar isT => let _ ← Sat.Solver.newVar true true isT
    | .phase l => modifyThe Sat.Solver (·.freezePolarity l)
    | .clause lits removable tag =>
      modifyThe PropState fun p => { p with base := p.base.push (lits, .cnf tag) }
      let _ ← Sat.Solver.addClause lits removable

/-- Run an operation of the engine outside the search. -/
def onEngineTop (x : EngineM α) : PropM α := do
  let a ← onEngine (do let a ← x; flushLemmas; return a)
  flushOpsTop
  return a

/-- `PropEngine`: assert the formulas, and solve. -/
def propSolve (formulas : List Node) : PropM Sat.Solver.Result := do
  let c ← read
  Sat.Solver.init
  onEngine do
    if c.eeSolver then
      let ctx ← eeCtx
      modify fun s => { s with ee := { EE.init ctx with dt := { enabled := c.dtSolver }, sets := { enabled := c.setsSolver }, strings := { enabled := c.stringsSolver } } }
  -- `PropEngine::finishInit`: `true` and `(not false)`, at level 0
  -- (the inputs of the certificate: these two, then the formulas)
  onEngineTop do
    let s0 ← newSatSource (.input 0)
    withCnf (Cnf.convertAndAssert (cnfHost c) Node.mkTrue false (src := s0))
    let s1 ← newSatSource (.input 1)
    withCnf (Cnf.convertAndAssert (cnfHost c) (Node.notNode Node.mkFalse) false (src := s1))
  -- the context level of `check-sat`
  onEngine pushLevel
  -- the node ids that the arithmetic solver approximates (by first occurrence)
  onEngine (modify fun s => { s with arith := formulas.foldl Arith.State.noteAges s.arith })
  -- `notifyInputFormulas`: the formulas go to the decision engine first, before
  -- the lemmas that their conversion may give
  -- (skolem definitions wait until they become relevant, `jh-skolem-rlv=ASSERT`)
  if c.decision != .internal then
    let mut defs : Std.HashMap Key Node := {}
    let mut plain := #[]
    for f in formulas do
      match skolemOfDefinition f with
      | some k => defs := defs.insert ⟨k⟩ f
      | none => plain := plain.push f
    let defs' := defs
    onEngine (modify fun s => { s with skDefs := defs' })
    let plain' := plain
    modifyThe PropState fun p => { p with dec := { p.dec.addAssertions plain' with mode := c.decision } }
  for (f, i) in formulas.zipIdx do
    onEngineTop do
      let src ← newSatSource (.input (i + 2))
      withCnf (Cnf.convertAndAssert (cnfHost c) f false (src := src))
  -- `TheoryProxy::presolve`: the decision engine's, then the theories'
  modifyThe PropState fun p => { p with dec := p.dec.presolve }
  if c.arithSolver then onEngineTop (withArith Arith.presolve)
  Sat.Solver.solve

/-- The inputs of the certificate of a refutation of `formulas`. -/
def certInputs (formulas : List Node) : Array Node :=
  #[Node.mkTrue, Node.notNode Node.mkFalse] ++ formulas.toArray

/-- After a refutation: the theory propagations at level 0 that the SAT solver
did not ask to explain are explained now (their reasons still hold), so that
the certificate has their clauses. Post hoc: nothing is printed. -/
def explainLevelZero : PropM Unit := do
  let s ← getThe Sat.Solver
  for p in s.trail do
    let d := s.vardata[p.var]!
    if d.level == 0 && d.reason == Sat.CRef.lazy then
      let n ← satNode p
      let (exp, tag) ← onEngine (satExplainQuiet n)
      let mut out := #[p]
      for e in (if exp.isEmpty then #[Node.mkTrue] else exp) do out := out.push (← satLit e).neg
      modifyThe PropState fun q => { q with base := q.base.push (out, tag) }

/-- **The certificate of a refutation**: the clauses as literals of terms, with
their justifications; those with none (lemmas with no proof) are left
out, and the check fails if the refutation needs them. -/
def buildCert (p : PropState) : Option SatProof.Cert := do
  let toNodes (c : Array Lit) : Option SatProof.Clause := c.mapM (Cnf.getNode? p.eng.cnf)
  let source (k : Nat) : Option SatProof.Just :=
    match p.eng.satSources[k]? with
    | some (.input i) => some (.input i)
    | some (.theory (some (A, q))) => some (.theory A q)
    | some (.lemma (some (F, q))) => some (.lemma F q)
    | some (.arith (some (A, q))) => some (.arith A q)
    | _ => none
  let mut clauses : Array (SatProof.Clause × SatProof.Just) := #[]
  -- the clauses that follow by unit propagation from the steps of their
  -- explanations, which come first among the learned clauses
  let mut derived : Array SatProof.Clause := #[]
  for (c, tag) in p.base do
    let aux := match tag with
      | .cnf (.src k) => match p.eng.satSources[k]? with
        | some (.derived aux) => some aux
        | _ => none
      | .derived aux => some aux
      | _ => none
    if let some aux := aux then
      for (d, j) in aux do
        if let some j := j then clauses := clauses.push (d, j)
      derived := derived.push (← toNodes c)
      continue
    let j := match tag with
      | .cnf (.defn n) => some (.defn n)
      | .cnf (.src k) => source k
      | .theory j => j
      | .derived _ => none
    if let some j := j then clauses := clauses.push ((← toNodes c), j)
  let learned ← p.learned.mapM toNodes
  return { clauses, learned := derived ++ learned }

/-- **Solve formulas** with the SAT solver and the theory engine. A `sat`
answer comes with the engine's state, from which the caller builds a model
(and checks it); the SAT solver's Boolean variables are added to the
literals asserted, with their values. An `unsat` answer is not certified yet
(that needs the SAT solver's refutation, `docs/theory-engine-plan.md`,
Stage 6), and so is `unknown`. -/
def runSat (c : Config) (formulas : List Node) : Result :=
  let c := { c with satMode := true, defer := false }
  let (r, p) := ((propSolve formulas).run c).run {}
  let e := p.eng
  if let some why := e.satError then
    { answer := .unknown, events := e.events, uncertified := some why }
  else match r with
  | .sat =>
    -- the values of the SAT solver's own Boolean variables
    let bools := e.cnf.booleanVariables.filterMap fun v =>
      match e.cnf.nodeToLit.get? ⟨v⟩ with
      | some l =>
        match p.sat.model[l.var]? with
        | some .tt => some v
        | some .ff => some (Node.notNode v)
        | _ => none
      | none => none
    -- arithmetic is solved if its relaxation is satisfiable and it met nothing
    -- unsupported
    let arithOk := c.arithSolver && e.arith.unsupported.isNone && e.arith.qflraStatus == .sat
    let solved := e.used.isEmpty || ((c.eeSolver || arithOk) &&
      e.used.all fun T => [.THEORY_UF, .THEORY_DATATYPES, .THEORY_SETS].contains T ||
        (T == .THEORY_ARITH && arithOk) ||
        -- strings, unless their last full-effort check was incomplete
        (T == .THEORY_STRINGS && c.stringsSolver && !e.ee.strings.incomplete) ||
        -- quantifiers, unless the model is unsound
        (T == .THEORY_QUANTIFIERS && c.quantSolver)) && e.modelUnsoundAt.isNone
    { answer := if solved then .sat else .unknown, events := e.events, ee := e.ee,
      asserted := e.asserted ++ bools, arithModel := if arithOk then Arith.modelValues e.arith else #[] }
  | .unsat =>
    -- the certificate, post hoc
    let p := ((explainLevelZero.run c).run p).2
    let inputs := certInputs formulas
    match buildCert p with
    | some cert =>
      if cert.check inputs then { answer := .unsat, events := e.events, satCert := some (inputs, cert) }
      else { answer := .unknown, events := e.events,
             uncertified := some s!"the certificate of the SAT solver's refutation does not check: {cert.why inputs}" }
    | none => { answer := .unknown, events := e.events,
                uncertified := some "a clause of the SAT solver's refutation has no literals of terms" }
  | .unknown => { answer := .unknown, events := e.events }

end Telos.Solver

namespace Telos.Solver

/-- **An `unsat` of the SAT solver is certified**: it comes with a certificate
of a refutation of the formulas that checks. -/
theorem runSat_unsat (c : Config) (fs : List Node) (h : (runSat c fs).answer = .unsat) :
    ∃ cert, (runSat c fs).satCert = some (certInputs fs, cert) ∧ cert.check (certInputs fs) = true := by
  revert h
  unfold runSat
  dsimp only
  repeat' split
  all_goals first
    | (intro h; simp_all)
    | (intro h; exact ⟨_, rfl, by assumption⟩)
    | (intro h; cases h)

end Telos.Solver
