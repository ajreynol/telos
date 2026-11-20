import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Preprocess.Options
import Telos.Solver.Event
import Telos.Solver.EqualityEngine
import Telos.Solver.Theory.UF
import Telos.Solver.EqBuild

/-!
# The theory engine, on conjunctions of literals

A port of cvc5's `TheoryEngine` (`src/theory/theory_engine.cpp`) for inputs with
no SAT structure: the preprocessed assertions are literals, which are asserted
one at a time, as cvc5's SAT solver does with unit clauses. A small stand-in
for the SAT solver keeps the values of the literals and the literals the
theories propagate.

What cvc5 does on such inputs, observed with `-o theory-events`
(`docs/theory-engine-plan.md`, "Stage 1"):

1. it preregisters `true` and `false` at level 0, then each atom at level 1, in
   assertion order (`TheoryEngine::preRegister`), each subterm with the
   theories that own it (`PreRegisterVisitor`);
2. if two literals contradict each other, the SAT solver answers `unsat`
   before asserting anything;
3. otherwise it asserts each literal, in order, to the theory of its atom;
4. it runs the theory engine's `check` at standard effort: each enabled theory's
   `check`, in cvc5's order, until no new facts are asserted. The theories'
   propagations go to the SAT solver. A propagated literal that is false
   is a conflict, explained by the theory (`explain`); one not yet assigned is
   assigned and asserted, and the checks run again;
5. then at full effort, likewise.

The only theory solver is UF (`Telos/Solver/Theory/UF.lean`) with the central
equality engine (`Telos/Solver/EqualityEngine.lean`), and only in logics where
it is the only theory, so that theory combination (sharing) is not needed.
Elsewhere the theories' checks do nothing, and the answer is `unknown` as soon
as a theory gets a literal.

The answers are not certified yet (milestone 3 of the plan): the events are
for comparison with cvc5.
-/

namespace Telos.Solver

/-- The theories that cvc5 enables for a logic, after `SetDefaults::widenLogic`
(observed with `-o theory-events`: the theories whose `check` cvc5 calls),
among those of safe mode. For `ALL`, cvc5 also enables finite fields, floating
point, separation logic and bags, which telos does not model: their checks do
nothing on inputs that do not use them, and `scripts/fuzz-solve.py` drops them
from cvc5's traces. A logic that requires one of them is not supported. -/
def enabledTheories (logic : String) : Except String (List Theory) := do
  let l ← Preprocess.Logic.parse logic
  let l := l.widen
  -- strings enable `strings-exp`, which needs quantifiers, and UF
  let l := if l.strings then { l with quantified := true, uf := true } else l
  let base := if logic.startsWith "QF_" then (logic.drop 3).toString else logic
  if base != "ALL" && l.others > 0 then
    throw s!"unsupported: the logic {logic} has theories outside safe mode"
  let on : Theory → Bool
    | .THEORY_BUILTIN | .THEORY_BOOL => true
    | .THEORY_UF => l.uf
    | .THEORY_ARITH => l.arith
    | .THEORY_BV => l.bv
    | .THEORY_ARRAYS => l.arrays
    | .THEORY_DATATYPES => l.datatypes
    | .THEORY_SETS => l.sets
    | .THEORY_STRINGS => l.strings
    | .THEORY_QUANTIFIERS => l.quantified
  return Theory.all.filter on

/-- The configuration of the engine. -/
structure Config where
  /-- The enabled theories, in cvc5's order. -/
  theories : List Theory
  /-- cvc5's `theoryof-mode` is `term` (`PPOptions.termBased`). -/
  termBased : Bool := false
  /-- Also record the central equality engine's notifications
  (`-o theory-events-ee`). -/
  eeEvents : Bool := false

/-- A Boolean term skolem (`Env::isBooleanTermSkolem`): the purification
skolem of a Boolean term in a term position, which term formula removal
introduces. cvc5 treats these as theory atoms of UF. In a replayed trace
(`Telos/Frontend/Replay.lean`) the skolems are the symbols that cvc5 printed,
named `@purify_k`. -/
def isBooleanTermSkolem (t : Node) : Bool :=
  match t with
  | .skolem .PURIFY _ => t.typeHint == some .boolean
  | .var name .boolean => name.startsWith "@purify_"
  | _ => false

/-- The theory that owns a term (`Env::theoryOf`): Boolean term skolems belong
to UF. -/
def Config.theoryOf (c : Config) (t : Node) : Theory :=
  let T := Theory.ofTheoryId (Preprocess.ppTheoryOf c.termBased t)
  if T == .THEORY_BOOL && isBooleanTermSkolem t then .THEORY_UF else T

/-- UF is solved: it is the only theory, so there is no sharing, and the logic
is quantifier-free. -/
def Config.ufSolver (c : Config) : Bool :=
  c.theories == [.THEORY_BUILTIN, .THEORY_BOOL, .THEORY_UF]

/-- The answer to `check-sat`. -/
inductive Answer where
  | sat
  | unsat
  | unknown
  deriving DecidableEq, Repr, Inhabited

def Answer.name : Answer → String
  | .sat => "sat"
  | .unsat => "unsat"
  | .unknown => "unknown"

/-- The stand-in for the SAT solver: the value of each assigned atom. -/
abbrev Assignment := Std.HashMap Key Bool

/-- The context-dependent state of the engine saved at a push (cvc5's `CDO`s
and `CDList`s: the theory engine's flags, the facts of the theories, the
propagated literals, the SAT assignment, the preregistration cache). -/
structure Saved where
  assignTrail : Nat
  preregLog : Nat
  ufFacts : Nat
  ufHead : Nat
  factsAsserted : Bool
  inConflict : Bool
  theoryConflict : Bool
  propagated : Nat
  asserted : Nat
  deriving Inhabited

structure State where
  events : Array Event := #[]
  /-- The SAT context level. -/
  level : Nat := 0
  assignment : Assignment := {}
  /-- The atoms registered with the SAT solver so far. -/
  registered : Std.HashSet Key := {}
  /-- The theories each term was preregistered with, as a set of theory
  indices (`PreRegisterVisitor::d_visited`). -/
  preregVisited : Std.HashMap Key Nat := {}
  /-- Facts were asserted to a theory since the last round of checks
  (`TheoryEngine::d_factsAsserted`). -/
  factsAsserted : Bool := false
  /-- `TheoryEngine::d_inConflict`. -/
  inConflict : Bool := false
  /-- A theory reported a conflict (rather than propagating a false literal). -/
  theoryConflict : Bool := false
  /-- The literals propagated to the SAT solver since it last looked
  (`TheoryEngine::d_propagatedLiterals`). -/
  propagated : Array Node := #[]
  /-- The theories that were given a literal. -/
  used : Array Theory := #[]
  /-- The literals asserted, in order. -/
  asserted : Array Node := #[]
  /-- UF's facts, and how many it has processed. -/
  ufFacts : Array Node := #[]
  ufHead : Nat := 0
  ee : EE.EqualityEngine := default
  /-- The atoms assigned, in order, for backtracking the assignment. -/
  assignTrail : Array Key := #[]
  /-- The previous values of the entries of `preregVisited` set, in order. -/
  preregLog : Array (Key × Option Nat) := #[]
  /-- The context-dependent state saved at each push: the `i`-th, when
  leaving level `i`. -/
  saved : Array Saved := #[]
  /-- The certificate of the conflict: its assumptions and a proof of
  `(true, false)` from them (`Telos/Solver/EqProof.lean`), or why there is
  none. -/
  cert : Except String (Array Node × EqProof) := .error "no conflict"

abbrev EngineM := ReaderT Config (StateM State)

def emit (e : Event) : EngineM Unit :=
  modify fun s => { s with events := s.events.push e }

def level : EngineM Nat := do return (← get).level

/-- The atom and polarity of a literal. -/
def atomOf (lit : Node) : Node × Bool :=
  match lit with
  | .app (.kind .NOT) #[a] => (a, false)
  | _ => (lit, true)

/-- Whether an atom is a theory atom, given to a theory solver, rather than a
Boolean variable, which only the SAT solver sees. -/
def isTheoryAtom (c : Config) (atom : Node) : Bool :=
  c.theoryOf atom != .THEORY_BOOL

/-- The equality engine's view of the engine. -/
def eeCtx : EngineM EE.Ctx := do
  let asg := (← get).assignment
  return { congruenceKinds := UF.congruenceKind, value := fun a => asg.get? ⟨a⟩ }

/-- Run an operation of the equality engine, and take its notes. -/
def runEE (x : EE.EEM α) : EngineM (α × Array EE.Note) := do
  let ctx ← eeCtx
  -- the engine's conflict flag, which is context dependent, is the source of truth
  let (ee, inConflict) ← modifyGet fun s => ((s.ee, s.inConflict), { s with ee := default })
  let (a, ee) := (x.run ctx).run { ee with notes := #[], teConflict := inConflict }
  let notes := ee.notes
  modify fun s => { s with ee := { ee with notes := #[] } }
  return (a, notes)

/-- `TheoryEngine::propagate` without sharing: the literal goes to the SAT
solver, unless it is already true there; a false one puts the engine in
conflict. -/
def propagate (T : Theory) (lit : Node) : EngineM Unit := do
  emit (.propagate (← level) T lit)
  if (← get).inConflict then return
  let (atom, pol) := atomOf lit
  match (← get).assignment.get? ⟨atom⟩ with
  | some v =>
    if v == pol then return
    modify fun s => { s with inConflict := true }
  | none => pure ()
  modify fun s => { s with propagated := s.propagated.push lit }

/-- Process the notes of the central equality engine
(`EqEngineManagerCentral`): its propagations and conflicts are
`THEORY_BUILTIN`'s. -/
def processNotes (notes : Array EE.Note) : EngineM Unit := do
  for n in notes do
    match n with
    | .newClass t => if (← read).eeEvents then emit (.eeNewClass (← level) t)
    | .merge a b => if (← read).eeEvents then emit (.eeMerge (← level) a b)
    | .disequal a b r => if (← read).eeEvents then emit (.eeDiseq (← level) a b r)
    | .propagate lit => propagate .THEORY_BUILTIN lit
    | .constantMerge a b =>
      -- `eqNotifyConstantTermMerge`: the conflict, explained
      let (exp, _) ← runEE (EE.explainLit (Node.eqNode a b))
      emit (.conflict (← level) .THEORY_BUILTIN "EQ_CONSTANT_MERGE" (EE.mkAnd exp))
      let cert := EE.conflictOfConstants (← get).ee (← get).asserted exp a b
      modify fun s => { s with inConflict := true, theoryConflict := true, cert }

/-- Run an operation of the equality engine and process its notes. -/
def withEE (x : EE.EEM α) : EngineM α := do
  let (a, notes) ← runEE x
  processNotes notes
  return a

/-- `Theory::preRegisterTerm` of theory `T`. -/
def theoryPreRegister (T : Theory) (t : Node) : EngineM Unit := do
  if T == .THEORY_UF && (← read).ufSolver then withEE (UF.preRegisterTerm t)

/-- The theory that owns a type (`Theory::theoryOf(TypeNode)`). -/
def typeTheory (T : TypeNode) : Theory := Theory.ofTheoryId T.theoryId

/-- Whether a type is finite (`Env::isFiniteType`), for the types telos's
solvers handle. -/
def isFiniteType : TypeNode → Bool
  | .boolean | .bitVector _ => true
  | _ => false

def theoryBit (T : Theory) : Nat := 1 <<< (Theory.all.idxOf T)

def hasTheory (set : Nat) (T : Theory) : Bool := (set >>> (Theory.all.idxOf T)) % 2 == 1

/-- `isAlreadyVisited` of the preregistration visitor. -/
def isAlreadyVisited (c : Config) (visited : Nat) (cur parent : Node) : Bool :=
  let ct := c.theoryOf cur
  if !hasTheory visited ct then false
  else if cur == parent then true
  else
    let pt := c.theoryOf parent
    if !hasTheory visited pt then false
    else match cur.typeHint with
      | some T => if ct == pt && !isFiniteType T then true else hasTheory visited (typeTheory T)
      | none => ct == pt

/-- `PreRegisterVisitor::alreadyVisited`. -/
def alreadyVisited (cur parent : Node) : EngineM Bool := do
  match parent with
  | .app (.kind k) _ =>
    if (k == .FORALL || k == .EXISTS) && cur != parent then return true
  | _ => pure ()
  match (← get).preregVisited.get? ⟨cur⟩ with
  | none => return false
  | some v => return isAlreadyVisited (← read) v cur parent

/-- Set the theories `cur` was preregistered with (a context-dependent map). -/
def setVisited (cur : Node) (v : Nat) : EngineM Unit :=
  modify fun s => { s with preregLog := s.preregLog.push (⟨cur⟩, s.preregVisited.get? ⟨cur⟩),
                           preregVisited := s.preregVisited.insert ⟨cur⟩ v }

/-- `PreRegisterVisitor::visit`: preregister `cur` with its theory, its
parent's, and its type's when they differ or the type is finite. -/
def visitPrereg (cur parent : Node) : EngineM Unit := do
  let c ← read
  let mut visited := (← get).preregVisited.getD ⟨cur⟩ 0
  let ct := c.theoryOf cur
  let mut ths : Array Theory := #[ct]
  if cur != parent then
    let pt := c.theoryOf parent
    ths := ths.push pt
    match cur.typeHint with
    | some T => if ct != pt || isFiniteType T then ths := ths.push (typeTheory T)
    | none => pure ()
  for T in ths do
    if !hasTheory visited T then
      visited := visited ||| theoryBit T
      setVisited cur visited
      theoryPreRegister T cur
  setVisited cur visited

/-- The children of a term, as cvc5 iterates them (without the operator). -/
def children : Node → Array Node
  | .app _ cs => cs
  | _ => #[]

/-- `NodeVisitor<PreRegisterVisitor>::run`: a post-order traversal, the children
pushed in order and so visited last first. -/
def preRegisterVisit (atom : Node) : EngineM Unit := do
  -- (node, parent, children added)
  let mut stack : Array (Node × Node × Bool) := #[(atom, atom, false)]
  while h : stack.size > 0 do
    let (cur, parent, added) := stack[stack.size - 1]
    if ← alreadyVisited cur parent then
      stack := stack.pop
    else if added then
      visitPrereg cur parent
      stack := stack.pop
    else
      stack := stack.set! (stack.size - 1) (cur, parent, true)
      for c in children cur do
        if !(← alreadyVisited c cur) then stack := stack.push (c, cur, false)

/-- `TheoryEngine::preRegister`, for an atom met by the CNF stream. -/
def preRegister (atom : Node) : EngineM Unit := do
  if (← get).registered.contains ⟨atom⟩ then return
  modify fun s => { s with registered := s.registered.insert ⟨atom⟩ }
  if !isTheoryAtom (← read) atom then return
  emit (.prereg (← level) atom)
  preRegisterVisit atom

/-- `Theory::assertFact`, via `TheoryEngine::assertFact`: the literal is given
to the theory of its atom. -/
def assertFact (lit : Node) : EngineM Unit := do
  let (atom, _) := atomOf lit
  let c ← read
  if !isTheoryAtom c atom then return
  let T := c.theoryOf atom
  emit (.assert (← level) T lit)
  modify fun s => { s with factsAsserted := true,
                           used := if s.used.contains T then s.used else s.used.push T }
  if T == .THEORY_UF then modify fun s => { s with ufFacts := s.ufFacts.push lit }

/-- The SAT solver assigns `lit` and asserts it. -/
def assign (lit : Node) : EngineM Unit := do
  let (atom, pol) := atomOf lit
  modify fun s => { s with assignment := s.assignment.insert ⟨atom⟩ pol,
                           assignTrail := s.assignTrail.push ⟨atom⟩,
                           asserted := s.asserted.push lit }
  assertFact lit

/-! ## Context levels -/

instance : Inhabited Key := ⟨⟨default⟩⟩

/-- Enter a new SAT context level (`Context::push`). -/
def pushLevel : EngineM Unit :=
  modify fun s =>
    let sv : Saved := ⟨s.assignTrail.size, s.preregLog.size, s.ufFacts.size, s.ufHead,
      s.factsAsserted, s.inConflict, s.theoryConflict, s.propagated.size, s.asserted.size⟩
    { s with saved := s.saved.push sv, level := s.level + 1, ee := EE.push s.ee }

/-- Return to the SAT context level `k` (`Context::pop`), restoring what was
saved when leaving it. -/
def popTo (k : Nat) : EngineM Unit :=
  modify fun s => Id.run do
    let some sv := s.saved[k]? | return s
    let mut asg := s.assignment
    for i in [sv.assignTrail:s.assignTrail.size] do
      asg := asg.erase s.assignTrail[i]!
    let mut pv := s.preregVisited
    for k' in [0:s.preregLog.size - sv.preregLog] do
      let (key, old) := s.preregLog[s.preregLog.size - 1 - k']!
      pv := match old with
        | some v => pv.insert key v
        | none => pv.erase key
    return { s with
      assignment := asg, assignTrail := s.assignTrail.take sv.assignTrail,
      preregVisited := pv, preregLog := s.preregLog.take sv.preregLog,
      ufFacts := s.ufFacts.take sv.ufFacts, ufHead := sv.ufHead,
      factsAsserted := sv.factsAsserted, inConflict := sv.inConflict,
      theoryConflict := sv.theoryConflict, propagated := s.propagated.take sv.propagated,
      asserted := s.asserted.take sv.asserted,
      saved := s.saved.take k, level := k, ee := EE.popTo s.ee k }

/-- Raise the context level to `k` (pushes are implicit in cvc5's traces). -/
def raiseTo (k : Nat) : EngineM Unit := do
  while (← get).level < k do pushLevel

/-- `Theory::check` of one theory: for UF, its facts are asserted to the
equality engine, until the engine is in conflict. -/
def theoryCheck (T : Theory) (e : Effort) : EngineM Unit := do
  emit (.check (← level) T e)
  if T == .THEORY_UF && (← read).ufSolver then
    repeat
      let s ← get
      if s.inConflict || s.ufHead ≥ s.ufFacts.size then break
      let fact := s.ufFacts[s.ufHead]!
      modify fun s => { s with ufHead := s.ufHead + 1 }
      withEE (UF.assertFact fact)

/-- `TheoryEngine::check`: rounds of checks of every enabled theory, while new
facts are asserted and there is no conflict. At full effort the first round
always runs. -/
def check (e : Effort) : EngineM Unit := do
  if e == .full then modify fun s => { s with factsAsserted := true }
  repeat
    let s ← get
    if !s.factsAsserted || s.inConflict then break
    modify fun s => { s with factsAsserted := false }
    for T in (← read).theories do
      if T.hasCheck then
        theoryCheck T e
        if (← get).inConflict then break

/-- The explanation of a propagated literal (`TheoryEngine::getExplanation`
without sharing: the theory of its atom explains it), as its assumptions. -/
def explain (lit : Node) : EngineM (Array Node) := do
  if (← read).ufSolver then
    let (exp, _) ← runEE (EE.explainLit lit)
    return exp
  return #[]

/-- The literal that makes `lit` false: its negation. -/
def negate (lit : Node) : Node :=
  match lit with
  | .app (.kind .NOT) #[a] => a
  | _ => Node.notNode lit

/-- What the SAT solver does with the propagated literals. -/
inductive SatResult where
  | conflict
  | newFacts
  | quiet

/-- The SAT solver takes the propagated literals: a false one is a conflict,
which it asks the theory to explain; unassigned ones are assigned and
asserted. -/
def satPropagate : EngineM SatResult := do
  let lits ← modifyGet fun s => (s.propagated, { s with propagated := #[] })
  let mut progress := false
  for lit in lits do
    let (atom, pol) := atomOf lit
    match (← get).assignment.get? ⟨atom⟩ with
    | some v =>
      if v != pol then
        let exp ← explain lit
        emit (.explain (← level) lit (EE.mkAnd exp))
        let cert := EE.conflictOfPropagation (← get).ee (← get).asserted exp lit (negate lit)
        modify fun s => { s with cert }
        return .conflict
    | none =>
      assign lit
      progress := true
  return if progress then .newFacts else .quiet

/-- Solve the conjunction of the literals `lits`, as cvc5's SAT solver does
with unit clauses. -/
def solve (lits : List Node) : EngineM Answer := do
  emit (.prereg 0 Node.mkTrue)
  emit (.prereg 0 Node.mkFalse)
  modify fun s => { s with registered := (s.registered.insert ⟨Node.mkTrue⟩).insert ⟨Node.mkFalse⟩ }
  if (← read).ufSolver then
    let ctx ← eeCtx
    modify fun s => { s with ee := EE.init ctx }
  if lits.contains Node.mkFalse then
    modify fun s => { s with cert := .ok (#[Node.mkFalse], .symm (.assume 0)) }
    return .unsat
  pushLevel
  for l in lits do preRegister (atomOf l).1
  -- the unit clauses: two that contradict each other are a conflict
  let mut units : Std.HashMap Key Bool := {}
  for l in lits do
    let (atom, pol) := atomOf l
    match units.get? ⟨atom⟩ with
    | some v =>
      if v != pol then
        -- the atom, asserted with both polarities
        let p : EqProof := match atom with
          | .app (.kind .EQUAL) #[_, _] => .trans (.symm (.eqTrue (.assume 0))) (.assume 1)
          | _ => .trans (.symm (.assume 0)) (.assume 1)
        modify fun s => { s with cert := .ok (#[atom, Node.notNode atom], p) }
        return .unsat
    | none => units := units.insert ⟨atom⟩ pol
  let mut seen : Std.HashSet Key := {}
  for l in lits do
    let (atom, _) := atomOf l
    if !seen.contains ⟨atom⟩ then
      seen := seen.insert ⟨atom⟩
      assign l
  let mut effort := Effort.standard
  repeat
    check effort
    if (← get).theoryConflict then return .unsat
    match ← satPropagate with
    | .conflict => return .unsat
    | .newFacts => effort := .standard
    | .quiet => if effort == .full then break else effort := .full
  let s ← get
  if s.used.isEmpty || ((← read).ufSolver && s.used.all (· == .THEORY_UF)) then
    return .sat
  return .unknown

/-! ## Replay -/

/-- An input event of a cvc5 trace (`-o theory-events`): what the SAT solver
and the theory engine ask of the theories. -/
inductive Input where
  | prereg (level : Nat) (atom : Node)
  | assert (level : Nat) (lit : Node)
  | check (level : Nat) (T : Theory) (e : Effort)
  | pop (level : Nat)
  /-- The SAT solver asks for the explanation of a propagated literal. -/
  | explain (level : Nat) (lit : Node)

/-- Replay one input. -/
def replayInput : Input → EngineM Unit
  | .prereg k atom => do
    if k == 0 then
      -- `true` and `false`, at the solver's initialization
      emit (.prereg 0 atom)
    else
      raiseTo k
      emit (.prereg k atom)
      preRegisterVisit atom
  | .assert k lit => do raiseTo k; assign lit
  | .check k T e => do raiseTo k; theoryCheck T e
  | .pop k => do popTo k; emit (.pop k)
  | .explain k lit => do
    raiseTo k
    emit (.explain k lit (EE.mkAnd (← explain lit)))

/-- **Replay** a cvc5 trace: give the theories the inputs that cvc5's SAT
solver and theory engine gave its theories, in order, and record telos's
events. The SAT solver's decisions and backtracking come from the trace, so
the theories are compared with cvc5's on inputs with SAT structure, without a
SAT solver. -/
def replay (c : Config) (inputs : List Input) : Array Event :=
  let act : EngineM Unit := do
    if c.ufSolver then
      let ctx ← eeCtx
      modify fun s => { s with ee := EE.init ctx }
    for i in inputs do replayInput i
  ((act.run c).run {}).2.events

/-- The result of the engine. -/
structure Result where
  answer : Answer
  events : Array Event
  /-- Why an `unsat` of the engine was not certified, and so answered
  `unknown`. -/
  uncertified : Option String := none
  /-- The certificate of an `unsat` answer. -/
  cert : Option (Array Node × EqProof) := none

/-- The certificate `(A, p)` refutes the literals `lits`: `p` proves
`(true, false)` from the closed assumptions `A`, all of which are among
`lits`. -/
def certifies (lits : List Node) (A : Array Node) (p : EqProof) : Bool :=
  A.all (fun l => lits.any (fun x => decide (x = l))) && EqProof.checkConflict A p

/-- Run `solve` on `lits`. An `unsat` answer stands only if its certificate
refutes `lits` (`certifies`), and is `unknown` otherwise. -/
def run (c : Config) (lits : List Node) : Result :=
  let (a, s) := ((solve lits).run c).run {}
  if a != .unsat then { answer := a, events := s.events } else
  match s.cert with
  | .error e => { answer := .unknown, events := s.events, uncertified := some e }
  | .ok (A, p) =>
    if certifies lits A p then { answer := .unsat, events := s.events, cert := some (A, p) }
    else { answer := .unknown, events := s.events, uncertified := some "the certificate does not check" }

/-- **An `unsat` answer is certified**: it comes with a certificate that
refutes the literals. (`verification/TelosProofs/Solver/Engine.lean` turns
this into: no well-formed model satisfies the literals.) -/
theorem run_unsat (c : Config) (lits : List Node) (h : (run c lits).answer = .unsat) :
    ∃ A p, certifies lits A p = true := by
  unfold run at h
  split at h
  split at h
  · simp_all
  · split at h
    · simp at h
    · rename_i A p _
      split at h
      · exact ⟨A, p, by assumption⟩
      · simp at h

end Telos.Solver
