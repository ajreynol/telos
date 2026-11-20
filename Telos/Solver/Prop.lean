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
  let q ← modifyGet fun s => (s.satQueue, { s with satQueue := #[] })
  for lit in q do
    modify fun s => { s with asserted := s.asserted.push lit }
    assertFact lit
  flushLemmas
  check e
  flushLemmas

/-- `TheoryEngine::getExplanation`, as the SAT solver asks for it: the
verified explanation (`EE.explainLitV`), or else the equality engine's. -/
def satExplain (lit : Node) : EngineM (Array Node) := do
  let exp ← match EE.explainLitV (← exCtx) lit with
    | some exp => pure exp
    | none =>
      modify fun s => { s with unverifiedExplains := s.unverifiedExplains + 1 }
      explain lit
  emit (.explain (← level) lit (EE.mkAnd exp))
  return exp

/-! ## The SAT solver's side -/

structure PropState where
  sat : Sat.Solver := {}
  eng : State := {}

abbrev PropM := ReaderT Config (StateM PropState)

instance : MonadStateOf Sat.Solver PropM where
  get := do return (← getThe PropState).sat
  set s := modifyThe PropState fun p => { p with sat := s }
  modifyGet f := modifyGetThe PropState fun p =>
    let sat := p.sat
    let p := { p with sat := {} }
    let (a, sat) := f sat
    (a, { p with sat })

/-- Run an operation of the engine. -/
def onEngine (x : EngineM α) : PropM α := do
  let c ← read
  let e ← modifyGetThe PropState fun p => (p.eng, { p with eng := {} })
  let (a, e) := (x.run c).run e
  modifyThe PropState fun p => { p with eng := e }
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
    | .clause lits removable =>
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
    let exp ← onEngineF (satExplain n)
    let mut out := #[l]
    for e in (if exp.isEmpty then #[Node.mkTrue] else exp) do out := out.push (← satLit e).neg
    return out
  enqueueTheoryLiteral l := do
    let n ← satNode l
    onEngine (enqueueSat n)
  contextPush := onEngine pushLevel
  contextPop := onEngine do
    let k := (← get).level - 1
    popTo k
    emit (.pop k)
  notifyBacktrack := onEngineF satBacktrack
  getNextDecisionRequest := pure (Lit.undef, false, false)
  isDecisionEngineDone := pure false
  theoryNeedCheck := onEngine do
    let s ← get
    return s.outputUsed || s.lemmasAdded
  notifySatClause _ := pure ()
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
    | .clause lits removable => let _ ← Sat.Solver.addClause lits removable

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
    if c.ufSolver then
      let ctx ← eeCtx
      modify fun s => { s with ee := { EE.init ctx with dt := { enabled := c.dtSolver } } }
  -- `PropEngine::finishInit`: `true` and `(not false)`, at level 0
  onEngineTop do
    withCnf (Cnf.convertAndAssert (cnfHost c) Node.mkTrue false)
    withCnf (Cnf.convertAndAssert (cnfHost c) (Node.notNode Node.mkFalse) false)
  -- the context level of `check-sat`
  onEngine pushLevel
  for f in formulas do
    onEngineTop (withCnf (Cnf.convertAndAssert (cnfHost c) f false))
  Sat.Solver.solve

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
    let solved := e.used.isEmpty || (c.ufSolver &&
      e.used.all ([.THEORY_UF, .THEORY_DATATYPES].contains ·))
    { answer := if solved then .sat else .unknown, events := e.events, ee := e.ee,
      asserted := e.asserted ++ bools }
  | .unsat =>
    { answer := .unknown, events := e.events,
      uncertified := some "an unsat of the SAT solver, which is not certified yet" }
  | .unknown => { answer := .unknown, events := e.events }

end Telos.Solver

namespace Telos.Solver

/-- The SAT solver's `unsat` is not certified yet: `runSat` never answers it. -/
theorem runSat_ne_unsat (c : Config) (fs : List Node) : (runSat c fs).answer ≠ .unsat := by
  unfold runSat
  dsimp only
  repeat' split
  all_goals simp

end Telos.Solver
