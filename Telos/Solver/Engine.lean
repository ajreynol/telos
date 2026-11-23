import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Preprocess.Options
import Telos.Solver.Event
import Telos.Solver.EqualityEngine
import Telos.Solver.Theory.UF
import Telos.Solver.Theory.Datatypes
import Telos.Solver.Theory.Sets
import Telos.Solver.Theory.StringsSolver
import Telos.Solver.Theory.Quantifiers
import Telos.Solver.EqBuild
import Telos.Solver.Explain
import Telos.Solver.Model
import Telos.Solver.Cnf
import Telos.Solver.SatProof
import Telos.Solver.DtLemma
import Telos.Solver.SetsLemma
import Telos.Solver.StringsLemma
import Telos.Solver.QuantLemma
import Telos.Solver.Theory.Arith.Solver
import Telos.Solver.Decision

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

/-- The linear solver's options of a logic (`SetDefaults`). -/
def arithOptionsOf (logic : String) : Arith.Options :=
  match Preprocess.Logic.parse logic with
  | .ok l => let l := l.widen; Arith.Options.ofLogic l.pureArith l.quantified l.linear l.integers l.difference
  | .error _ => Arith.Options.ofLogic false true false true false

/-- `SetDefaults::setDefaultDecisionMode`: justification for `ALL`,
quantifiers, strings, QF_LRA, the logics of bit-vectors with UF or arrays,
QF_BV, and QF_AUFLIA; stop-only for QF_LRA and QF_AUFLIA; internal (MiniSat's
own decisions) otherwise. `--decision=MODE` overrides it. -/
def decisionModeOf (logic : String) (user : Option String := none) : Decision.Mode :=
  match user with
  | some "internal" => .internal
  | some "justification" => .justification
  | some "stoponly" => .stopOnly
  | _ =>
    match Preprocess.Logic.parse logic with
    | .error _ => .internal
    | .ok l =>
      let all := l == Preprocess.Logic.all
      let l := l.widen
      let qfLra := !l.quantified && l.pureArith && l.linear && !l.difference && !l.integers
      let qfAuflia := !l.quantified && l.arrays && l.uf && l.arith
      let justification := all ||
        (!l.quantified && l.bv && l.numTheories == 1) ||
        (!l.quantified && (l.arrays || l.uf) && l.bv) ||
        qfAuflia || qfLra || l.quantified || l.strings
      let stopOnly := !(all || l.strings) && (qfAuflia || qfLra)
      if !justification then .internal else if stopOnly then .stopOnly else .justification

/-- The configuration of the engine. -/
structure Config where
  /-- The enabled theories, in cvc5's order. -/
  theories : List Theory
  /-- cvc5's `theoryof-mode` is `term` (`PPOptions.termBased`). -/
  termBased : Bool := false
  /-- Also record the central equality engine's notifications
  (`-o theory-events-ee`). -/
  eeEvents : Bool := false
  /-- Print the triggers made (`-o trigger`). -/
  triggerEvents : Bool := false
  /-- Record the events (off when only the answer is wanted: `telos --solve`). -/
  events : Bool := true
  /-- Leave the explanation of a conflict to `run`, which certifies it
  (`certifyV`), rather than explaining it when it happens. -/
  defer : Bool := false
  /-- Build the certificate of an `unsat` (`EqProof`), for the CPC proof. -/
  wantProof : Bool := false
  /-- Replaying a trace: the inputs, including the shared equalities asserted
  to the theories, come from it. -/
  replaying : Bool := false
  /-- Fidelity to cvc5 where it only decides the form of what is produced, not
  the reasoning: imitate cvc5's order of nodes (by id) to orient the equalities
  of shared terms and of lemma atoms, and rewrite lemma atoms as cvc5's
  preprocessing does. On for fuzzing and replay, where the events must be
  cvc5's; a fast mode may turn it off (the answers are certified either way). -/
  cvc5Order : Bool := true
  /-- A SAT solver drives the engine (`Telos/Solver/Prop.lean`): the atoms get
  their SAT literals from the CNF stream, which preregisters them; lemmas and
  conflicts become clauses. -/
  satMode : Bool := false
  /-- The linear solver's options that the logic decides. -/
  arith : Arith.Options := {}
  /-- The SAT solver's decision mode. -/
  decision : Decision.Mode := .internal
  /-- The declared constants, by their order of declaration (cvc5's node ids). -/
  declOrder : Std.HashMap String Nat := {}
  /-- cvc5's node ids, approximated (`NodeOrder`), for the rewriter. -/
  order : NodeOrder := {}

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

/-- The theories are solved: they are among UF and datatypes, and the logic is
quantifier-free. -/
def Config.ufSolver (c : Config) : Bool :=
  c.theories.all ([.THEORY_BUILTIN, .THEORY_BOOL, .THEORY_UF, .THEORY_DATATYPES].contains ·)

/-- Theory combination is on (`LogicInfo::isSharingEnabled`): more than one
theory other than the builtin, Boolean and quantifier theories. -/
def Config.sharing (c : Config) : Bool :=
  (c.theories.filter fun T => ![.THEORY_BUILTIN, .THEORY_BOOL, .THEORY_QUANTIFIERS].contains T).length > 1

/-- The linear arithmetic solver is on (`Telos/Solver/Theory/Arith/`): arithmetic
is enabled. -/
def Config.arithSolver (c : Config) : Bool := c.theories.contains .THEORY_ARITH

/-- The engine and the SAT solver handle the enabled theories (some only in
part: arithmetic answers `unknown` until its solver is complete): they are
among UF, datatypes and arithmetic, and the logic is quantifier-free. -/
def Config.satSupported (c : Config) : Bool :=
  c.theories.all fun T => [.THEORY_BUILTIN, .THEORY_BOOL, .THEORY_UF, .THEORY_DATATYPES, .THEORY_ARITH,
    .THEORY_SETS, .THEORY_STRINGS].contains T ||
    -- quantifiers (Stage 10; strings enable them, `strings-exp`)
    T == .THEORY_QUANTIFIERS

/-- The central equality engine runs, with UF and datatypes: the theories are
supported (with arithmetic or not). -/
def Config.eeSolver (c : Config) : Bool := c.satSupported

/-- The theory of datatypes is enabled, and solved. -/
def Config.dtSolver (c : Config) : Bool := c.eeSolver && c.theories.contains .THEORY_DATATYPES

/-- The theory of sets is enabled, and solved (`Telos/Solver/Theory/Sets.lean`). -/
def Config.setsSolver (c : Config) : Bool := c.eeSolver && c.theories.contains .THEORY_SETS

/-- The theory of strings is enabled (`Telos/Solver/Theory/Strings.lean`, in
progress). -/
def Config.stringsSolver (c : Config) : Bool := c.eeSolver && c.theories.contains .THEORY_STRINGS

/-- The quantifiers engine is enabled, and solved (in part,
`Telos/Solver/Theory/Quantifiers.lean`). -/
def Config.quantSolver (c : Config) : Bool := c.eeSolver && c.theories.contains .THEORY_QUANTIFIERS

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

/-- A conflict whose explanation is left to `run` (`Config.defer`). -/
inductive Pending where
  /-- A propagated literal that is false. -/
  | prop (lit : Node)
  /-- A merge of the constants `a` and `b` in the equality engine. -/
  | constants (a b : Node)
  /-- A conflict of the theory of datatypes (its event is already emitted). -/
  | dt (cf : DT.Conflict)
  /-- A conflict or a lemma of linear arithmetic, with its certificate. -/
  | arith (cert : LinCert)
  /-- A conflict of the theory of sets: its inference and the conflict sent. -/
  | sets (id : String) (conf : Node)
  /-- A conflict of the theory of strings: its inference and its premises
  before their explanation. -/
  | strings (id : String) (premises : Array Node)
  /-- A lemma of the quantifiers engine, rewritten at cvc5's node order (its
  instance's nodes numbered as the substitution makes them): not oriented
  again. -/
  | quant
  deriving Inhabited

/-- The source of a formula given to the CNF stream (`Cnf.ClauseTag.src`), for
the certificate of a refutation. -/
inductive SatSource where
  /-- The input formula of this index. -/
  | input (i : Nat)
  /-- A theory lemma, as given to the CNF stream, with a proof of `(F, true)`
  (`Telos/Solver/DtLemma.lean`), if any. -/
  | lemma (cert : Option (Node × EqProof))
  /-- The negation of a theory conflict, with its certificate, if any. -/
  | theory (cert : Option (Array Node × EqProof))
  /-- A conflict of linear arithmetic, or a lemma's clause, with its
  certificate, if any (`SatProof.Just.arith`). -/
  | arith (cert : Option (Array Node × LinCert))
  /-- A clause that follows by unit propagation from these clauses, with their
  certificates (`stepClauses`). -/
  | derived (aux : Array (Array Node × Option SatProof.Just))
  deriving Inhabited

/-- The context-dependent state of the engine saved at a push (cvc5's `CDO`s
and `CDList`s: the theory engine's flags, the facts of the theories, the
propagated literals, the SAT assignment, the preregistration cache). -/
structure Saved where
  assignTrail : Nat
  preregLog : Nat
  ufFacts : Nat
  ufHead : Nat
  dtFacts : Nat
  dtHead : Nat
  setsFacts : Nat
  setsHead : Nat
  stringsFacts : Nat
  stringsHead : Nat
  arithFacts : Nat
  arithHead : Nat
  factsAsserted : Bool
  inConflict : Bool
  theoryConflict : Bool
  propagated : Nat
  asserted : Nat
  sharedLog : Nat
  registerLog : Nat
  skActive : Nat
  ufFunctionTerms : Nat
  arithShared : Nat
  setsShared : Nat
  stringsShared : Nat
  deriving Inhabited

/-- An undo entry of the shared terms database and the propagation marks (cvc5's
context-dependent maps). -/
inductive SharedUndo where
  | atomTerms (atom : Key) (old : Option (Array Node))
  | termTheories (k : Key × Key) (old : Option Nat)
  | notified (t : Key) (old : Option Nat)
  | marked (lit : Key)
  | markedBuiltin (lit : Key)
  | sharedArith (lit : Key)
  | propagator (lit : Key)
  deriving Inhabited

structure State where
  /-- The SAT solver is searching (MiniSat's `minisat_busy`): the clauses of a
  lemma are queued, and its unit clauses are not assigned yet. -/
  satBusy : Bool := false
  events : Array Event := #[]
  /-- The linear arithmetic solver (`Telos/Solver/Theory/Arith/`). -/
  arith : Arith.State := {}
  /-- The SAT context level. -/
  level : Nat := 0
  assignment : Assignment := {}
  /-- The atoms registered with the SAT solver (context dependent, as a lemma's
  atoms are registered again after a backtrack), and their order. -/
  registered : Std.HashSet Key := {}
  /-- The atoms waiting to be preregistered (`d_preregisterQueue`), and whether
  one is being preregistered (`d_inPreregister`): an atom met while another is
  (the atom of a lemma sent then) is preregistered after it. -/
  preregQueue : Array Node := #[]
  inPrereg : Bool := false
  registerLog : Array Key := #[]
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
  /-- The explanations for which the verified one did not apply. -/
  unverifiedExplains : Nat := 0
  /-- The conflict left to `run`. -/
  pending : Option Pending := none
  /-- The atoms registered, in order: the roots of the verified explanations
  (`EE.explainLitV`), with a path below them to each of their subterms. -/
  atoms : Array Node := #[]
  atomPaths : Std.HashMap Key SubPath := {}
  /-- UF's facts, and how many it has processed. -/
  ufFacts : Array Node := #[]
  ufHead : Nat := 0
  /-- The facts of the theory of datatypes, and how many it has processed. -/
  dtFacts : Array Node := #[]
  dtHead : Nat := 0
  /-- The facts asserted to the theory of sets (`Theory::d_facts`), and the
  next to process. -/
  setsFacts : Array Node := #[]
  setsHead : Nat := 0
  /-- The facts asserted to the theory of strings, and the next to process. -/
  stringsFacts : Array Node := #[]
  stringsHead : Nat := 0
  /-- The quantifiers engine (`Telos/Solver/Theory/Quantifiers.lean`), its facts
  and how many it processed, and their sizes saved at each push. -/
  quant : Quant.Eng := {}
  quantFacts : Array Node := #[]
  quantHead : Nat := 0
  quantSaved : Array (Nat × Nat) := #[]
  /-- The level at which a theory set the model unsound (`TheoryEngine::d_modelUnsound`,
  context dependent): the answer is then `unknown`. -/
  modelUnsoundAt : Option Nat := none
  /-- The facts of arithmetic, and how many it has processed (context
  dependent). -/
  arithFacts : Array Node := #[]
  arithHead : Nat := 0
  /-- A theory sent a lemma, which `solve` cannot use (it has no SAT solver). -/
  lemmaSent : Bool := false
  /-- The shared terms database (`SharedTermsDatabase`): the shared terms of
  each atom, the theories that share each, and those already notified. -/
  atomTerms : Std.HashMap Key (Array Node) := {}
  termTheories : Std.HashMap (Key × Key) Nat := {}
  notified : Std.HashMap Key Nat := {}
  /-- The literals propagated to the SAT solver, and those asserted to the
  central equality engine's theories (`d_propagationMap`, by target). -/
  markedSat : Std.HashSet Key := {}
  markedBuiltin : Std.HashSet Key := {}
  /-- The literals the shared solver asserted to arithmetic: the equality
  engine explains them (`d_propagationMap` has them from `THEORY_BUILTIN`). -/
  sharedArith : Std.HashSet Key := {}
  /-- The theory that propagated each literal to the SAT solver first, which
  explains it (`d_propagationMap`). -/
  propagator : Std.HashMap Key Theory := {}
  sharedLog : Array SharedUndo := #[]
  /-- The lemmas sent, whose atoms are to be preregistered (`flushLemmas`). -/
  lemmaQueue : Array Node := #[]
  /-- In a replay: inside a call of `TheoryEngine::check`, and whether the last
  check was of the last theory of a round. -/
  inCheckCall : Bool := false
  lastWasLast : Bool := false
  /-- In a replay: the literals propagated in the last call of the checks, that
  the SAT solver is to assert, in order. -/
  pendingProps : Array Node := #[]
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
  -- with a SAT solver (`Config.satMode`):
  /-- The CNF stream. -/
  cnf : Cnf.State := {}
  /-- The literals the SAT solver assigned, to be asserted at the next check
  (`TheoryProxy::d_queue`). -/
  satQueue : Array Node := #[]
  /-- The theory atoms that got SAT literals, with the context level at which
  they were preregistered (`TheoryPreregistrar::d_sat_literals`). -/
  satLiterals : Array (Node × Nat) := #[]
  /-- The lemmas and conflicts (`true`, with a certificate) to give to the CNF
  stream. -/
  satLemmaQueue : Array (Node × Bool × Option Pending × Option EqProof) := #[]
  /-- The sources of the formulas given to the CNF stream. -/
  satSources : Array SatSource := #[]
  /-- The formulas given to the decision engine since it last took them (the
lemmas, as `TheoryProxy::notifyAssertion`), and the skolem definitions that
became active (its local assertions). -/
  decisionQueue : Array Node := #[]
  decisionLocalQueue : Array Node := #[]
  /-- The skolem definitions (`SkolemDefManager`): of each skolem, and those
  active (context dependent, in order). -/
  skDefs : Std.HashMap Key Node := {}
  skActive : Array Node := #[]
  skActiveSet : Std.HashSet Key := {}
  /-- UF's function applications (`d_functionsTerms`, context dependent), for
  its care graph. -/
  ufFunctionTerms : Array Node := #[]
  /-- Arithmetic's shared terms (its `TheoryState::getSharedTerms`, context
  dependent), in order. -/
  arithShared : Array Node := #[]
  /-- The shared terms of the theory of sets (`Theory::d_sharedTerms`). -/
  setsShared : Array Node := #[]
  /-- The shared terms of the theory of strings (`shared_terms_begin`). -/
  stringsShared : Array Node := #[]
  /-- The lemmas the builtin theory sent (the combination splits), rewritten
  (its inference manager's cache). -/
  builtinLemmas : Std.HashSet Key := {}
  /-- A skolem definition became active in the last check
  (`d_activatedSkDefs`). -/
  activatedSkDefs : Bool := false
  /-- The outputs of the linear solver left to `flushArithDeferred`. -/
  arithDeferred : Array Arith.Output := #[]
  /-- `TheoryEngine::d_outputChannelUsed` and `d_lemmasAdded`, since the last
  check. -/
  outputUsed : Bool := false
  lemmasAdded : Bool := false
  /-- Something the SAT solver cannot be given (a literal with no SAT
  literal): the answer is then `unknown`. -/
  satError : Option String := none

abbrev EngineM := ReaderT Config (StateM State)

def emit (e : Event) : EngineM Unit := do
  if (← read).events then modify fun s => { s with events := s.events.push e }

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
  let dt := (← read).dtSolver
  let sets := (← read).setsSolver
  let strs := (← read).stringsSolver
  let ord := (← read).order
  let base : EE.Ctx := { congruenceKinds := fun k => UF.congruenceKind k || (dt && DT.congruenceKind k) ||
                                                     (sets && Sets.congruenceKind k) ||
                                                     (strs && Strings.congruenceKind k),
                         interpretedKinds := fun k => strs && Strings.interpretedKind k,
                         evaluate := fun t => Telos.rewrite t ord,
                         value := fun a => asg.get? ⟨a⟩, cvc5Order := (← read).cvc5Order,
                         declOrder := (← read).declOrder, order := (← read).order }
  -- the theories' handlers, in the order of their ids
  let onNote := fun n ee =>
    let ee := if dt then DT.onNote base n ee else ee
    let ee := if sets then Sets.onNote base n ee else ee
    if strs then Strings.onNote base n ee else ee
  return if dt || sets || strs then { base with onNote } else base

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
  modify fun s => { s with outputUsed := true }
  if (← get).inConflict then return
  let (atom, pol) := atomOf lit
  if (← read).sharing then
    -- with sharing, only a SAT literal goes to the SAT solver, once
    if let .app (.kind .EQUAL) _ := atom then
      if !(← get).registered.contains ⟨atom⟩ then return
    if (← get).markedSat.contains ⟨lit⟩ then return
    modify fun s => { s with markedSat := s.markedSat.insert ⟨lit⟩, sharedLog := s.sharedLog.push (.marked ⟨lit⟩) }
  match (← get).assignment.get? ⟨atom⟩ with
  | some v =>
    if v == pol then return
    modify fun s => { s with inConflict := true }
  | none => pure ()
  if !(← get).propagator.contains ⟨lit⟩ then
    modify fun s => { s with propagator := s.propagator.insert ⟨lit⟩ T,
                             sharedLog := s.sharedLog.push (.propagator ⟨lit⟩) }
  modify fun s => { s with propagated := s.propagated.push lit }

/-- The key of a literal in the record of the literals given to theories
(`markPropagation`): the central equality engine's theories share one record;
arithmetic has its own (its unary-`and` wrapper cannot be a literal). -/
def markKey (T : Theory) (lit : Node) : Key :=
  if T == .THEORY_ARITH then ⟨Node.mkNode .AND #[lit]⟩ else ⟨lit⟩

/-- An equality literal with its sides swapped. -/
def flipEq : Node → Node
  | .app (.kind .EQUAL) #[a, b] => Node.eqNode b a
  | .app (.kind .NOT) #[.app (.kind .EQUAL) #[a, b]] => Node.notNode (Node.eqNode b a)
  | n => n

/-- `TheoryEngine::assertToTheory` of a shared equality, from the shared
solver to the theory `T`: normalized, and asserted unless it already was. -/
def assertShared (T : Theory) (lit : Node) : EngineM Unit := do
  if (← get).inConflict then return
  -- cvc5 asserts the (cvc5-oriented) literal, even if it rewrites to `true`;
  -- one that rewrites to `false` is a conflict (`CONFLICT_REWRITE_LIT`)
  if Telos.rewrite lit == Node.mkFalse then
    emit (.conflict (← level) T "CONFLICT_REWRITE_LIT" Node.mkFalse)
    let why := "a conflict of a shared literal that rewrites to false, which is not certified yet"
    modify fun s => { s with inConflict := true, theoryConflict := true, cert := .error why }
    if (← read).satMode then
      modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (lit, true, none, none),
                               outputUsed := true, lemmasAdded := true }
    return
  let norm := lit
  -- (cvc5's record is keyed by the literal itself; the flipped equality is
  -- also taken as given while telos's orientation of equalities between
  -- applications only approximates cvc5's node ids)
  let marked := (← get).markedBuiltin
  if marked.contains (markKey T norm) then return
  if !(← read).stringsSolver && marked.contains (markKey T (flipEq norm)) then return
  modify fun s => { s with markedBuiltin := s.markedBuiltin.insert (markKey T norm),
                           sharedLog := s.sharedLog.push (.markedBuiltin (markKey T norm)),
                           factsAsserted := true,
                           used := if s.used.contains T then s.used else s.used.push T }
  emit (.assert (← level) T norm)
  if T == .THEORY_ARITH then
    modify fun s => { s with sharedArith := s.sharedArith.insert ⟨norm⟩,
                             sharedLog := s.sharedLog.push (.sharedArith ⟨norm⟩) }
  if T == .THEORY_DATATYPES then modify fun s => { s with dtFacts := s.dtFacts.push norm }
  if T == .THEORY_SETS then modify fun s => { s with setsFacts := s.setsFacts.push norm }
  if T == .THEORY_STRINGS then modify fun s => { s with stringsFacts := s.stringsFacts.push norm }
  if T == .THEORY_ARITH then modify fun s => { s with arithFacts := s.arithFacts.push norm }

/-- A context of the quantifiers engine that sees nothing (for the term
database's operations that do not look at the equality engine). -/
def Quant.emptyCtx : Quant.Ctx :=
  { hasTerm := fun _ => false, rep := id, areEqual := (· == ·), areDisequal := fun _ _ => false,
    lt := Node.lt, reps := #[], facts := #[], rewrite := id }

/-- Run an operation of the quantifiers' term database that does not look at
the equality engine. -/
def quantTermDb (x : Quant.M Unit) : EngineM Unit :=
  modify fun s =>
    let q := s.quant
    let s := { s with quant := {} }
    let (_, r) := (x.run Quant.emptyCtx).run { st := q.st }
    { s with quant := { q with st := r.st } }

/-- Process the notes of the central equality engine
(`EqEngineManagerCentral`): its propagations and conflicts are
`THEORY_BUILTIN`'s. -/
def processNotes (notes : Array EE.Note) : EngineM Unit := do
  for n in notes do
    match n with
    | .newClass t =>
      if (← read).eeEvents then emit (.eeNewClass (← level) t)
      -- (`TermRegistry::eqNotifyNewClass`)
      if (← read).quantSolver then quantTermDb (Quant.addTerm t)
    | .merge a b =>
      -- (with the central equality engine, the quantifiers engine is notified of
      -- new classes only, not of merges: `EqEngineManagerCentral`)
      if (← read).eeEvents then emit (.eeMerge (← level) a b)
    | .disequal a b r => if (← read).eeEvents then emit (.eeDiseq (← level) a b r)
    | .propagate lit => propagate .THEORY_BUILTIN lit
    | .constantMerge a b =>
      -- `eqNotifyConstantTermMerge`: the conflict, explained now or by `run`
      if (← read).defer then
        modify fun s => { s with pending := some (.constants a b) }
      else
        let (exp, _) ← runEE (EE.explainLit (Node.eqNode a b))
        emit (.conflict (← level) .THEORY_BUILTIN "EQ_CONSTANT_MERGE" (EE.mkAnd exp))
        if (← read).satMode then
          modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (EE.mkAnd exp, true, some (.constants a b), none),
                                   outputUsed := true, lemmasAdded := true }
      modify fun s => { s with inConflict := true, theoryConflict := true }
    | .fact T id lit exp => emit (.fact (← level) T id lit exp)
    | .skolem k => emit (.skolem k)
    | .lemma T id lem =>
      emit (.lemma (← level) T id lem)
      if (← read).satMode then
        let ord := (← read).order
        let fresh := (← get).ee.freshIds
        let proof := if T == .THEORY_SETS then SetsLemma.prove id lem ord
          else if T == .THEORY_STRINGS then
            -- the order in which the theory rewrote the lemma's parts
            StringsLemma.prove id lem { ord with fresh }
          else DtLemma.prove id lem
        modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (lem, false, none, proof),
                                 outputUsed := true, lemmasAdded := true }
      else
        modify fun s => { s with lemmaSent := true, lemmaQueue := s.lemmaQueue.push lem,
                                 lemmasAdded := true }
    | .sharedEq tag lit =>
      -- `propagateSharedEquality`: asserted to the theory of the tag, then and
      -- there (a replay skips the trace's copy)
      if tag == Theory.THEORY_DATATYPES.tag then
        assertShared .THEORY_DATATYPES lit
      else if tag == Theory.THEORY_ARITH.tag && (← read).arithSolver then
        assertShared .THEORY_ARITH lit
      else if tag == Theory.THEORY_STRINGS.tag && (← read).stringsSolver then
        assertShared .THEORY_STRINGS lit
    | .conflict T id exp =>
      emit (.conflict (← level) T id exp)
      if (← read).satMode then
        let ee := (← get).ee
        let kind := if T == .THEORY_DATATYPES then ee.dt.conflict.map Pending.dt
          else if T == .THEORY_SETS then ee.sets.conflict.map fun (id, conf, _) => Pending.sets id conf
          else if T == .THEORY_STRINGS then ee.strings.conflict.map fun (id, _, ps) => Pending.strings id ps
          else none
        -- sets' conflict, as the theory engine explains it (`getExplanation`)
        let exp := if T == .THEORY_SETS then
            (ee.sets.conflict.map fun (_, _, a) => EE.mkAnd a).getD exp
          else exp
        modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (exp, true, kind, none),
                                 outputUsed := true, lemmasAdded := true }
      let why := s!"a conflict of {T.name}, which is not certified yet"
      modify fun s => { s with inConflict := true, theoryConflict := true, cert := .error why }
      if (← read).defer && T == .THEORY_DATATYPES then
        if let some cf := (← get).ee.dt.conflict then
          modify fun s => { s with pending := some (.dt cf) }

/-- Run an operation of the equality engine and process its notes. -/
def withEE (x : EE.EEM α) : EngineM α := do
  let (a, notes) ← runEE x
  processNotes notes
  return a

/-- What the quantifiers engine sees of the rest: the equality engine (its
terms, representatives, (dis)equalities and classes, in its order), cvc5's
node order, the facts asserted to the theories, and the rewriter. -/
def quantCtx : EngineM Quant.Ctx := do
  let s ← get
  let c ← read
  let ee := s.ee
  let ectx ← eeCtx
  let rep (t : Node) : Node := match ee.nodeIds.get? ⟨t⟩ with
    | some i => ee.nodes[EE.find ee i]!
    | none => t
  let areEqual (a b : Node) : Bool := a == b || match ee.nodeIds.get? ⟨a⟩, ee.nodeIds.get? ⟨b⟩ with
    | some i, some j => EE.find ee i == EE.find ee j
    | _, _ => false
  let areDisequal (a b : Node) : Bool := (((EE.areDisequal a b false).run ectx).run ee).1
  let mut reps : Array Node := #[]
  for i in [0:ee.nodes.size] do
    if !ee.isInternal[i]! && EE.find ee i == i then reps := reps.push ee.nodes[i]!
  let ord := { c.order with fresh := ee.freshIds }
  let members (r : Node) : Array Node := Id.run do
    let some i := ee.nodeIds.get? ⟨r⟩ | return #[r]
    let mut out := #[]
    let mut j := i
    for _ in [0:ee.nodes.size] do
      if !ee.isInternal[j]! then out := out.push ee.nodes[j]!
      j := ee.enodes[j]!.next
      if j == i then break
    return out
  return { hasTerm := fun t => ee.nodeIds.contains ⟨t⟩, rep, areEqual, areDisequal, members,
           order := c.order, rewriteAt := fun o t => Telos.rewrite t o,
           lt := fun a b => match ord.id? a, ord.id? b with
             | some i, some j => i < j
             | _, _ => EE.ageLt ee.nodeIds a b c.declOrder c.order,
           reps,
           facts := s.ufFacts ++ s.arithFacts ++ s.dtFacts ++ s.setsFacts ++ s.stringsFacts ++ s.quantFacts,
           rewrite := fun t => Telos.rewrite t ord }

/-- Run an operation of the quantifiers engine, and act on its outputs: its
skolems, and its lemmas, as a theory's (`TheoryEngine::lemma`); a model that
is unsound (`setModelUnsound`), and a check asked for (`markUsed`). -/
def quantRun (x : Quant.EM α) (flush : EngineM Unit := pure ()) : EngineM α := do
  let ctx ← quantCtx
  let q ← modifyGet fun s => (s.quant, { s with quant := {} })
  let q := { q with fresh := (← get).ee.freshIds }
  let ((a, q), out) := ((x.run q).run {}).run ctx
  modify fun s => { s with quant := { q with fresh := {} }, ee := { s.ee with freshIds := q.fresh } }
  processNotes (out.skolems.map EE.Note.skolem)
  -- the triggers made (`-o trigger`), printed when made, before the lemmas
  -- pending (`doPending`)
  if (← read).triggerEvents then
    for (_, t) in out.triggers do
      match t with
      | .trigger q ns tag u => emit (.trigger q ns tag u)
      | .noTrigger q => emit (.noTrigger q)
  -- each lemma, then its atoms preregistered (`TheoryEngine::lemma`)
  for l in out.lemmas do
    emit (.lemma (← level) .THEORY_QUANTIFIERS l.id l.lem)
    if (← read).satMode then
      modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (l.lem, false, some .quant, QuantLemma.prove l),
                               outputUsed := true, lemmasAdded := true }
    else
      modify fun s => { s with lemmaSent := true, lemmaQueue := s.lemmaQueue.push l.lem, lemmasAdded := true }
    flush
  if out.modelUnsound then
    let l ← level
    emit (.modelUnsound l .THEORY_QUANTIFIERS "QUANTIFIERS")
    modify fun s => { s with modelUnsoundAt := s.modelUnsoundAt.orElse fun _ => some l }
  if out.markUsed then modify fun s => { s with outputUsed := true }
  return a

/-- The proof of an `ARITH_EQUIV_ATOM` lemma `(= lit atom)`, two equalities
with the same normal form (`rewriter::normalizeEquality`, certified by
`arith_poly_norm_rel`; cvc5's `mkArithPolyNormRel`): each side's rewrite to
it, by transitivity. -/
def equivAtomProof (o : NodeOrder) (lem : Node) : Option EqProof := do
  let .app (.kind .EQUAL) #[lit, atom] := lem | none
  let side (x : Node) : Option (Node × Option EqProof) :=
    match Telos.Arith.normalizeEquality x o with
    | some r => do
      let cs ← Proof.cmdsOf r
      some (r.1, some (.valid (Node.eqNode x r.1) cs))
    | none => some (x, none)
  let (n₁, p₁) ← side lit
  let (n₂, p₂) ← side atom
  if n₁ != n₂ then none
  let q ← match p₁, p₂ with
    | some a, some b => some (EqProof.trans a (.symm b))
    | some a, none => some a
    | none, some b => some (.symm b)
    | none, none => none
  let p := EqProof.eqTrue q
  if EqProof.check #[] p == some (lem, Node.mkTrue) then some p else none

/-- What the engine does with an output of the linear solver, but for the
literals it ensures (`flushArithDeferred`). -/
def arithOutput (o : Arith.Output) : EngineM Unit := do
  match o with
  | .lemma id lem cert =>
    emit (.lemma (← level) .THEORY_ARITH id lem)
    if (← read).satMode then
      let ao := (← read).arith.order
      let fr := (← get).ee.freshIds
      let proof := if id == "ARITH_EQUIV_ATOM" then equivAtomProof { ao with fresh := fr } lem else none
      modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (lem, false, cert.map .arith, proof),
                               outputUsed := true, lemmasAdded := true }
    else
      modify fun s => { s with lemmaSent := true, lemmaQueue := s.lemmaQueue.push lem, lemmasAdded := true }
  | .conflict id exp cert =>
    -- `TheoryEngine::conflict`: each conflict is printed and is a clause
    emit (.conflict (← level) .THEORY_ARITH id exp)
    if (← read).satMode then
      modify fun s => { s with satLemmaQueue := s.satLemmaQueue.push (exp, true, cert.map .arith, none),
                               outputUsed := true, lemmasAdded := true }
    let why := s!"a conflict of THEORY_ARITH, which is not certified yet"
    modify fun s => { s with inConflict := true, theoryConflict := true, cert := .error why }
  | .propagate lit => do
    propagate .THEORY_ARITH lit
    -- an equality goes to the shared terms database too, now
    -- (`assertToTheory(literal, literal, THEORY_BUILTIN, theory)`)
    let c ← read
    let (atom, pol) := atomOf lit
    if c.sharing && c.eeSolver && atom.getKind == .EQUAL && !(← get).inConflict then
      let k : Key := ⟨lit⟩
      if !(← get).markedBuiltin.contains k then
        modify fun s => { s with markedBuiltin := s.markedBuiltin.insert k,
                                 sharedLog := s.sharedLog.push (.markedBuiltin k) }
        withEE (do let _ ← EE.assertEquality atom pol lit)
  | .scopePop => emit (.pop (← level))
  | .phase .. | .ensureLiteral _ => pure ()  -- (`flushArithDeferred`)

/-- Run an operation of the linear solver, and act on its outputs in order:
its lemmas (`TheoryInferenceManager::trustedLemma`) go to the CNF stream, as
the other theories' do. From a literal it
ensures (`Valuation::ensureLiteral`, which needs the CNF stream) on, they are
left to `flushArithDeferred`, which the caller (`theoryCheck`) runs next. -/
def withArith (x : Arith.ArithM α) : EngineM α := do
  let st ← modifyGet fun s => (s.arith, { s with arith := {} })
  let c ← read
  -- the nodes built during solving are numbered by the equality engine
  let st := { st with opts := { c.arith with order := { c.arith.order with fresh := (← get).ee.freshIds } } }
  let (a, st) := x.run st
  modify fun s => { s with ee := { s.ee with freshIds := st.opts.order.fresh } }
  let outs := st.outputs
  modify fun s => { s with arith := { st with outputs := #[] } }
  for o in outs do
    let deferring := !(← get).arithDeferred.isEmpty || match o with
      | .ensureLiteral _ => true
      | _ => false
    if deferring then modify fun s => { s with arithDeferred := s.arithDeferred.push o }
    else arithOutput o
  if let some why := st.unsupported then
    modify fun s => { s with satError := s.satError <|> some s!"arithmetic: {why}" }
  return a

/-- The theory that owns a type (`Theory::theoryOf(TypeNode)`). -/
def typeTheory (T : TypeNode) : Theory := Theory.ofTheoryId T.theoryId

/-- Whether a type is finite (`Env::isFiniteType`), for the types telos's
solvers handle. -/
def isFiniteType (T : TypeNode) : Bool := DT.isFiniteType T

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
def setVisited (cur : Node) (v : Nat) : EngineM Unit := do
  -- take the map and the log out of the state, so that they are updated in place
  let (pv, log) ← modifyGet fun s =>
    ((s.preregVisited, s.preregLog), { s with preregVisited := {}, preregLog := #[] })
  let old := pv.get? ⟨cur⟩
  let pv := pv.insert ⟨cur⟩ v
  let log := log.push (⟨cur⟩, old)
  modify fun s => { s with preregVisited := pv, preregLog := log }

/-- The children of a term, as cvc5 iterates them (without the operator). -/
def children : Node → Array Node
  | .app _ cs => cs
  | _ => #[]

/-- `SharedTermsDatabase::addSharedTerm`: `term` of `atom` is shared by the
theories `theories`. -/
def addSharedTerm (atom term : Node) (theories : Nat) : EngineM Unit := do
  let k : Key × Key := (⟨atom⟩, ⟨term⟩)
  let s ← get
  match s.termTheories.get? k with
  | none =>
    let old := s.atomTerms.get? ⟨atom⟩
    modify fun s => { s with
      atomTerms := s.atomTerms.insert ⟨atom⟩ ((old.getD #[]).push term),
      termTheories := s.termTheories.insert k theories,
      sharedLog := (s.sharedLog.push (.atomTerms ⟨atom⟩ old)).push (.termTheories k none) }
  | some old =>
    modify fun s => { s with termTheories := s.termTheories.insert k (theories ||| old),
                             sharedLog := s.sharedLog.push (.termTheories k (some old)) }

/-- `SharedSolver::preNotifySharedFact`: the theories sharing the terms of the
atom, not yet notified, are notified (`Theory::addSharedTerm`, which makes them
trigger terms of the central equality engine), and so is the shared terms
database (`markNotified`). -/
def preNotifySharedFact (atom : Node) : EngineM Unit := do
  let some terms := (← get).atomTerms.get? ⟨atom⟩ | return
  for term in terms do
    let s ← get
    let all := s.termTheories.getD (⟨atom⟩, ⟨term⟩) 0
    let old := s.notified.get? ⟨term⟩
    let newly := all ^^^ (all &&& old.getD 0)
    -- `Theory::addSharedTerm`, of each theory: `notifySharedTerm` (arithmetic
    -- sets the term up), then the trigger term, for the theories with an
    -- equality engine
    for T in Theory.all do
      if !hasTheory newly T then continue
      let arith := T == .THEORY_ARITH && (← read).arithSolver
      if arith then
        modify fun s => { s with arithShared := s.arithShared.push term }
        withArith (Arith.notifySharedTerm term)
      let sets := T == .THEORY_SETS && (← read).setsSolver
      if sets then modify fun s => { s with setsShared := s.setsShared.push term }
      let strs := T == .THEORY_STRINGS && (← read).stringsSolver
      if strs then modify fun s => { s with stringsShared := s.stringsShared.push term }
      if (← read).eeSolver && (T == .THEORY_UF || T == .THEORY_DATATYPES || arith || sets || strs) then
        withEE (EE.addTriggerTerm term T.tag)
    -- `SharedTermsDatabase::markNotified`: the trigger terms again
    if newly != 0 then
      modify fun s => { s with notified := s.notified.insert ⟨term⟩ (newly ||| old.getD 0),
                               sharedLog := s.sharedLog.push (.notified ⟨term⟩ old) }
      if (← read).eeSolver then
        for T in Theory.all do
          if hasTheory newly T then withEE (EE.addTriggerTerm term T.tag)

/-- Add a registered atom to the roots of the explanations. -/
def addRoot (atom : Node) : EngineM Unit := do
  -- take the array and the map out of the state, so that they are updated in place
  let (atoms, paths) ← modifyGet fun s => ((s.atoms, s.atomPaths), { s with atoms := #[], atomPaths := {} })
  let atoms := atoms.push atom
  let paths := EE.subtermPaths atoms paths (atoms.size - 1)
  modify fun s => { s with atoms, atomPaths := paths }

/-- The context of the verified explanations. -/
def exCtx : EngineM EE.ExCtx := do
  let s ← get
  return { ee := s.ee, roots := s.atoms, paths := s.atomPaths }

/-- `Theory::assertFact`, via `TheoryEngine::assertFact`: the literal is given
to the theory of its atom. -/
def assertFact (lit : Node) (fromSat : Bool := true) (to : Option Theory := none) : EngineM Unit := do
  let (atom, _) := atomOf lit
  let c ← read
  if !isTheoryAtom c atom then return
  if fromSat && c.sharing then preNotifySharedFact atom
  -- the literal is marked as asserted to the central equality engine's
  -- theories; a theory is not given it twice (`markPropagation`)
  let T := to.getD (c.theoryOf atom)
  let marked := (← get).markedBuiltin
  -- (the flipped equality too, but with strings, where telos's orientation
  -- of equalities follows cvc5's node ids closely enough to keep them apart,
  -- as cvc5 does)
  if marked.contains (markKey T lit) || (!c.stringsSolver && marked.contains (markKey T (flipEq lit))) then return
  modify fun s => { s with markedBuiltin := s.markedBuiltin.insert (markKey T lit),
                           sharedLog := s.sharedLog.push (.markedBuiltin (markKey T lit)) }
  emit (.assert (← level) T lit)
  modify fun s => { s with factsAsserted := true,
                           used := if s.used.contains T then s.used else s.used.push T }
  if T == .THEORY_UF then modify fun s => { s with ufFacts := s.ufFacts.push lit }
  if T == .THEORY_DATATYPES then modify fun s => { s with dtFacts := s.dtFacts.push lit }
  if T == .THEORY_SETS then modify fun s => { s with setsFacts := s.setsFacts.push lit }
  if T == .THEORY_STRINGS then modify fun s => { s with stringsFacts := s.stringsFacts.push lit }
  if T == .THEORY_ARITH then modify fun s => { s with arithFacts := s.arithFacts.push lit }
  if T == .THEORY_QUANTIFIERS then modify fun s => { s with quantFacts := s.quantFacts.push lit }
  -- an equality goes to the shared solver too (`THEORY_BUILTIN`), unless its
  -- theory uses the central equality engine (it is marked already): asserted
  -- to the equality engine now (`SharedTermsDatabase::assertShared`)
  if fromSat && c.sharing && c.eeSolver && atom.getKind == .EQUAL && T == .THEORY_ARITH then
    let k : Key := ⟨lit⟩
    if !(← get).markedBuiltin.contains k then
      modify fun s => { s with markedBuiltin := s.markedBuiltin.insert k,
                               sharedLog := s.sharedLog.push (.markedBuiltin k) }
      let (_, pol) := atomOf lit
      withEE (do let _ ← EE.assertEquality atom pol lit)

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
      s.dtFacts.size, s.dtHead, s.setsFacts.size, s.setsHead, s.stringsFacts.size, s.stringsHead, s.arithFacts.size, s.arithHead, s.factsAsserted, s.inConflict, s.theoryConflict, s.propagated.size, s.asserted.size,
      s.sharedLog.size, s.registerLog.size, s.skActive.size, s.ufFunctionTerms.size, s.arithShared.size,
      s.setsShared.size, s.stringsShared.size⟩
    { s with saved := s.saved.push sv, level := s.level + 1, ee := EE.push s.ee, arith := s.arith.push,
             quant := { s.quant with st := s.quant.st.push },
             quantSaved := s.quantSaved.push (s.quantFacts.size, s.quantHead) }

/-- A purification skolem (as `--post-asserts` names it in a script read back). -/
def isPurifySkolem : Node → Bool
  | .skolem .PURIFY _ => true
  | .var name _ => name.startsWith "@purify_"
  | _ => false

/-- The skolem a formula defines, if it is a skolem definition of term formula
removal: `(ite c (= k t₁) (= k t₂))` for an `ite` term, `(= k t)` for a
Boolean term. -/
def skolemOfDefinition (f : Node) : Option Node :=
  let sides : Node → Array Node
    | .app (.kind .EQUAL) #[a, b] => #[a, b]
    | _ => #[]
  match f with
  | .app (.kind .ITE) #[_, e1, e2] =>
    (sides e1).find? fun k => isPurifySkolem k && (sides e2).contains k
  | .app (.kind .EQUAL) #[a, b] =>
    if isPurifySkolem a && a.typeHint == some .boolean then some a
    else if isPurifySkolem b && b.typeHint == some .boolean then some b else none
  | _ => none

/-- `SkolemDefManager::notifyAsserted`: the definitions of the skolems of an
asserted literal that were not active, now active. -/
def activateSkolems (lit : Node) : EngineM (Array Node) := do
  let s ← get
  if s.skDefs.isEmpty || s.skActive.size == s.skDefs.size then return #[]
  let mut out := #[]
  let mut visit := #[lit]
  let mut seen : Std.HashSet Key := {}
  while !visit.isEmpty do
    let cur := visit.back!
    visit := visit.pop
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    if let some d := s.skDefs.get? ⟨cur⟩ then
      if !(← get).skActiveSet.contains ⟨d⟩ && !out.contains d then out := out.push d
      continue
    match cur with
    | .app _ cs => visit := visit ++ cs
    | _ => pure ()
  modify fun s => { s with skActive := s.skActive ++ out, skActiveSet := out.foldl (·.insert ⟨·⟩) s.skActiveSet }
  return out

/-- Return to the SAT context level `k` (`Context::pop`), restoring what was
saved when leaving it. -/
def popTo (k : Nat) : EngineM Unit := do
  let some sv := (← get).saved[k]? | return
  -- take the maps and the engine out of the state, so that they are updated in
  -- place, not copied
  let (asg, pv, ee) ← modifyGet fun s =>
    ((s.assignment, s.preregVisited, s.ee), { s with assignment := {}, preregVisited := {}, ee := default })
  let st ← get
  let mut asg := asg
  for i in [sv.assignTrail:st.assignTrail.size] do
    asg := asg.erase st.assignTrail[i]!
  let mut pv := pv
  for k' in [0:st.preregLog.size - sv.preregLog] do
    let (key, old) := st.preregLog[st.preregLog.size - 1 - k']!
    pv := match old with
      | some v => pv.insert key v
      | none => pv.erase key
  let ee := EE.popTo ee k
  modify fun s => { s with arith := Id.run do
    let mut a := s.arith
    while a.marks.size > k do a := a.pop
    return a }
  -- the shared terms database and the propagation marks
  let (at₀, tt₀, nt₀, ms₀, mb₀, log) ← modifyGet fun s =>
    ((s.atomTerms, s.termTheories, s.notified, s.markedSat, s.markedBuiltin, s.sharedLog),
     { s with atomTerms := {}, termTheories := {}, notified := {}, markedSat := {}, markedBuiltin := {},
              sharedLog := #[] })
  let mut at₀ := at₀
  let mut tt₀ := tt₀
  let mut nt₀ := nt₀
  let mut ms₀ := ms₀
  let mut mb₀ := mb₀
  for k' in [0:log.size - sv.sharedLog] do
    match log[log.size - 1 - k']! with
    | .atomTerms a old => at₀ := match old with
      | some v => at₀.insert a v
      | none => at₀.erase a
    | .termTheories key old => tt₀ := match old with
      | some v => tt₀.insert key v
      | none => tt₀.erase key
    | .notified t old => nt₀ := match old with
      | some v => nt₀.insert t v
      | none => nt₀.erase t
    | .marked l => ms₀ := ms₀.erase l
    | .markedBuiltin l => mb₀ := mb₀.erase l
    | .sharedArith l => modify fun s => { s with sharedArith := s.sharedArith.erase l }
    | .propagator l => modify fun s => { s with propagator := s.propagator.erase l }
  modify fun s => { s with atomTerms := at₀, termTheories := tt₀, notified := nt₀, markedSat := ms₀,
                           markedBuiltin := mb₀, sharedLog := log.take sv.sharedLog }
  -- the atoms registered above level `k`
  let (reg, rlog) ← modifyGet fun s => ((s.registered, s.registerLog), { s with registered := {}, registerLog := #[] })
  let mut reg := reg
  for i in [sv.registerLog:rlog.size] do reg := reg.erase rlog[i]!
  modify fun s => { s with registered := reg, registerLog := rlog.take sv.registerLog }
  -- the skolem definitions activated above level `k`
  modify fun s =>
    let gone := s.skActive.extract sv.skActive s.skActive.size
    { s with skActive := s.skActive.take sv.skActive,
             ufFunctionTerms := s.ufFunctionTerms.take sv.ufFunctionTerms,
             arithShared := s.arithShared.take sv.arithShared,
             setsShared := s.setsShared.take sv.setsShared,
             stringsShared := s.stringsShared.take sv.stringsShared,
             skActiveSet := gone.foldl (·.erase ⟨·⟩) s.skActiveSet }
  modify fun s => { s with
    assignment := asg, assignTrail := s.assignTrail.take sv.assignTrail,
    preregVisited := pv, preregLog := s.preregLog.take sv.preregLog,
    ufFacts := s.ufFacts.take sv.ufFacts, ufHead := sv.ufHead,
    dtFacts := s.dtFacts.take sv.dtFacts, dtHead := sv.dtHead,
    setsFacts := s.setsFacts.take sv.setsFacts, setsHead := sv.setsHead,
    stringsFacts := s.stringsFacts.take sv.stringsFacts, stringsHead := sv.stringsHead,
    arithFacts := s.arithFacts.take sv.arithFacts, arithHead := sv.arithHead,
    factsAsserted := sv.factsAsserted, inConflict := sv.inConflict,
    theoryConflict := sv.theoryConflict, propagated := s.propagated.take sv.propagated,
    asserted := s.asserted.take sv.asserted,
    saved := s.saved.take k, level := k, ee, satQueue := #[] }
  modify fun s =>
    let (qf, qh) := s.quantSaved[k]?.getD (s.quantFacts.size, s.quantHead)
    { s with quant := { s.quant with st := s.quant.st.popTo k }, quantFacts := s.quantFacts.take qf,
             quantHead := qh, quantSaved := s.quantSaved.take k,
             modelUnsoundAt := s.modelUnsoundAt.filter (· ≤ k) }

/-- Raise the context level to `k` (pushes are implicit in cvc5's traces). -/
def raiseTo (k : Nat) : EngineM Unit := do
  while (← get).level < k do pushLevel

/-- The atoms of a formula, as the CNF stream meets them: left to right, through
the Boolean connectives. -/
partial def formulaAtoms (n : Node) (acc : Array Node) : Array Node :=
  match n with
  | .app (.kind k) cs =>
    let bool := cs.all (·.typeHint == some .boolean)
    if k == .NOT || k == .AND || k == .OR || k == .IMPLIES || k == .XOR || k == .ITE ||
        (k == .EQUAL && bool) then
      cs.foldl (fun a c => formulaAtoms c a) acc
    else if acc.contains n then acc else acc.push n
  | .const (.boolean _) => acc
  | _ => if acc.contains n then acc else acc.push n

/-- A literal that `explainAllSteps` explained other than as a literal of the
SAT solver: by the linear solver (`arith`, with the certificate of the
explanation), or by the equality engine. -/
structure ExplainStep where
  lit : Node
  exp : Array Node
  arith : Bool
  cert : Option LinCert := none
  deriving Inhabited

/-- The explanation of literals as literals the SAT solver asserted: each
literal that it did not assert (all of them, with `all`; else all but the
first) is explained by the equality engine, in turn, until all are;
conjunctions are split, and `true` dropped (`TheoryEngine::getExplanation`).
With `record`, also the steps: each literal the linear solver explained, and
each literal the equality engine explained that is one of `lits` or of a linear
solver's explanation (the others are below an explanation of the equality
engine, which proves them from the literals of the SAT solver). -/
def explainAllSteps (lits : Array Node) (all : Bool) (record : Bool) :
    EngineM (Array Node × Array ExplainStep) := do
  let asg := (← get).assignment
  let fromSat (l : Node) : Bool :=
    let (a, p) := atomOf l
    asg.get? ⟨a⟩ == some p
  let mut out : Array Node := #[]
  let mut steps : Array ExplainStep := #[]
  -- each literal, and whether it is one of `lits` or of an arithmetic explanation
  let mut todo : Array (Node × Bool) := lits.map (·, true)
  let mut seen : Std.HashSet Key := {}
  let mut i := 0
  while i < todo.size do
    let (l, top) := todo[i]!
    let forced := !all && i == 0
    i := i + 1
    if seen.contains ⟨l⟩ then continue
    seen := seen.insert ⟨l⟩
    if l == Node.mkTrue || l == Node.notNode Node.mkFalse then continue
    let c ← read
    -- (a shared literal that the equality engine asserted to arithmetic is
    -- the equality engine's: `d_propagationMap` has it from THEORY_BUILTIN,
    -- even if it became a literal of the SAT solver after, which is then
    -- assigned after what arithmetic propagated from it)
    let sa := (← get).sharedArith
    let shared := c.arithSolver && sa.contains ⟨l⟩
    if !forced && !shared && fromSat l then
      if !out.contains l then out := out.push l
      continue
    match l with
    | .app (.kind .AND) cs => todo := todo ++ cs.map (·, top)
    | _ =>
      if c.arithSolver && c.theoryOf (atomOf l).1 == .THEORY_ARITH && !shared then
        -- `TheoryArith::explain`
        let e ← withArith (Arith.explain l)
        if record && !forced then
          steps := steps.push { lit := l, exp := e, arith := true, cert := ← withArith (Arith.explainCert l) }
        todo := todo ++ e.map (·, true)
      else
        let (exp, _) ← runEE (EE.explainLit l)
        -- (a shared literal that the SAT solver asserted to the equality
        -- engine is its own explanation there: the SAT solver's literal)
        if shared && exp.contains l && fromSat l then
          if !out.contains l then out := out.push l
          continue
        if record && !forced && top then steps := steps.push { lit := l, exp, arith := false }
        todo := todo ++ exp.map (·, false)
  return (out, steps)

def explainAll (lits : Array Node) (all : Bool) : EngineM (Array Node) :=
  return (← explainAllSteps lits all false).1

/-- The clause `[lit, ¬lit₀]`, for literals with the same polarity whose atoms
have the same rewrite, with its certificate: the refutation of `¬lit` and
`lit₀`. It relates a literal of a lemma as a theory stated it (`lit₀`) to the
literal of its rewrite (`lit`). -/
def rewriteClause (lit lit₀ : Node) : Option (Array Node × SatProof.Just) :=
  let (a, pos) := atomOf lit
  let (a₀, pos₀) := atomOf lit₀
  if pos != pos₀ || Telos.rewrite a != Telos.rewrite a₀ then none else
  -- `(l, true)` from the assumption `i`, the literal `l`
  let isTrue (i : Nat) (l : Node) : EqProof := match l with
    | .app (.kind .EQUAL) #[_, _] => .eqTrue (.assume i)
    | _ => .assume i
  let same : EqProof := .trans (.rw a) (.symm (.rw a₀))
  let A := #[negate lit, lit₀]
  -- (`(a, false)` and `(a₀, true)`, or `(a, true)` and `(a₀, false)`)
  let q : EqProof := if pos then .trans (.symm (.trans same (isTrue 1 a₀))) (.assume 0)
    else .trans (.symm (isTrue 0 a)) (.trans same (.assume 1))
  if EqProof.checkConflict A q then some (#[lit, negate lit₀], .theory A q) else none

/-- The clauses of the steps of an explanation (`explainAllSteps`) whose
literals of the SAT solver are `out`, with their certificates: for a literal
the linear solver explained, its explanation and the literal; for one the
equality engine explained, the literal from `out` and the literals the linear
solver explained (from the literals of the clause only). With them, the clause
of a certificate over the literals explained gives the clause over `out` by
unit propagation. -/
def stepClauses (out : Array Node) (steps : Array ExplainStep) :
    EngineM (Array (Array Node × Option SatProof.Just)) := do
  let ints := (steps.filter (·.arith)).map (·.lit)
  let ee := (← get).ee
  return steps.map fun st =>
    if st.arith then
      ((st.exp.map negate).push st.lit, st.cert.map (.arith (st.exp.push (negate st.lit))))
    else
      let E := (out ++ ints).filter (· != st.lit)
      match EE.conflictOfPropagation ee (E.push (negate st.lit)) E st.lit (negate st.lit) with
      | .ok (A, q) => (A.map negate, some (.theory A q))
      | .error _ => ((E.map negate).push st.lit, none)

/-! ### The CNF stream (`Config.satMode`) -/

/-- Run an operation of the CNF stream, on the stream of the state. -/
def withCnf (x : StateT Cnf.State EngineM α) : EngineM α := do
  let c ← modifyGet fun s => (s.cnf, { s with cnf := {} })
  let (a, c) ← x.run c
  modify fun s => { s with cnf := c }
  return a

/-- `Valuation::hasSatValue`: the atom is assigned, or, before the search, a
unit clause of it waits for the SAT solver (which assigns it when it is added,
as a lemma's conjunct is, before the lemma's atoms are preregistered); during
the search, MiniSat queues the clauses of a lemma (`addClause_` when
`minisat_busy`), so its units have no value yet. -/
def hasSatValue (atom : Node) : EngineM Bool := do
  let s ← get
  if s.assignment.contains ⟨atom⟩ then return true
  if s.satBusy then return false
  let some l := s.cnf.nodeToLit.get? ⟨atom⟩ | return false
  return s.cnf.ops.any fun
    | .clause ls _ _ => ls.size == 1 && ls[0]!.var == l.var
    | _ => false

/-- Run an operation of the engine from the CNF stream: the stream goes back
in the state meanwhile, as the operation may use it (a lemma's atoms). -/
def atEngine (x : EngineM α) : StateT Cnf.State EngineM α := do
  let c ← modifyGetThe Cnf.State fun c => (c, {})
  (modify fun s => { s with cnf := c } : EngineM Unit)
  let a ← (x : EngineM α)
  let c ← (modifyGet fun s => (s.cnf, { s with cnf := {} }) : EngineM Cnf.State)
  set c
  return a

/-- The equalities of a formula oriented as cvc5's node ids would (see
`flushLemmas`). -/
partial def orientEqs (ids : Std.HashMap Key Nat) (n : Node) (decl : Std.HashMap String Nat := {}) : Node :=
  match n with
  | .app (.kind .EQUAL) #[l, r] =>
    if l.typeHint == some .boolean then .app (.kind .EQUAL) #[orientEqs ids l decl, orientEqs ids r decl]
    -- (an arithmetic equality is oriented by its normal form, a set or string
    -- equality by node order, by the rewriter)
    else if l.typeHint == some .integer || l.typeHint == some .real then n
    else if (match l.typeHint with | some (.set _) | some .string => true | _ => false) then n
    else if EE.ageLt ids r l decl then Node.eqNode r l else n
  | .app (.kind k) cs =>
    if Cnf.isConnective n || k == .NOT then .app (.kind k) (cs.map (orientEqs ids · decl)) else n
  | _ => n

/-- A new source of clauses, by index. -/
def newSatSource (src : SatSource) : EngineM Nat :=
  modifyGet fun s => (s.satSources.size, { s with satSources := s.satSources.push src })

/-- The engine as the CNF stream's host. -/
def cnfHostWith (notify : Node → EngineM Unit) (c : Config) : Cnf.Host (StateT Cnf.State EngineM) where
  notifySatLiteral atom := atEngine (notify atom)
  isInternalBoolVar n :=
    c.theoryOf n == .THEORY_BOOL && match n with
      | .var .. | .skolem .. => true
      | _ => false

/-! ### Preregistration and lemmas (mutually recursive: a theory may send a lemma while it preregisters a term, whose atoms are preregistered then) -/

mutual
partial def theoryPreRegister (T : Theory) (t : Node) : EngineM Unit := do
  if T == .THEORY_ARITH && (← read).arithSolver then withArith (Arith.preRegisterTerm t)
  if T == .THEORY_UF && (← read).eeSolver then
    withEE (UF.preRegisterTerm t)
    -- (`d_functionsTerms`)
    if let .app (.node .APPLY_UF _) _ := t then
      modify fun s => { s with ufFunctionTerms := s.ufFunctionTerms.push t }
  if T == .THEORY_DATATYPES && (← read).dtSolver then withEE (DT.preRegisterTerm t)
  if T == .THEORY_SETS && (← read).setsSolver then withEE (Sets.preRegisterTerm t)
  if T == .THEORY_QUANTIFIERS && (← read).quantSolver && t.getKind == .FORALL then
    quantRun (Quant.preRegister t)
  if T == .THEORY_STRINGS && (← read).stringsSolver then
    -- each lemma's atoms are preregistered as it is sent
    let c ← read
    let ops : Strings.Ops EngineM := {
      run := fun x => do let a ← withEE x; flushLemmas; pure a
      hasSatValue := hasSatValue
      phase := fun n pol => do
        emit (.phase (← level) n pol)
        if c.satMode then withCnf (Cnf.preferPhase n pol) }
    Strings.preRegisterTerm ops t

/-- `PreRegisterVisitor::visit`: preregister `cur` with its theory, its
parent's, and its type's when they differ or the type is finite. -/
partial def visitPrereg (cur parent : Node) : EngineM Unit := do
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

/-- `NodeVisitor<PreRegisterVisitor>::run`: a post-order traversal, the children
pushed in order and so visited last first. -/
partial def preRegisterVisit (atom : Node) : EngineM Unit := do
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

/-- `NodeVisitor<SharedTermsVisitor>::run`: preregistration with sharing, by a
traversal of the atom of its own (`d_visited`), with the context-dependent
record of the theories each term was preregistered with (`d_preregistered`);
a term visited by a theory other than its own is a shared term of the atom. -/
partial def sharedVisit (atom : Node) : EngineM Unit := do
  let c ← read
  let mut visited : Std.HashMap Key Nat := {}
  let isVisited (visited : Std.HashMap Key Nat) (cur parent : Node) : Bool :=
    let closure := match parent with
      | .app (.kind k) _ => (k == .FORALL || k == .EXISTS) && cur != parent
      | _ => false
    closure || match visited.get? ⟨cur⟩ with
      | none => false
      | some v => isAlreadyVisited c v cur parent
  let mut stack : Array (Node × Node × Bool) := #[(atom, atom, false)]
  while h : stack.size > 0 do
    let (cur, parent, added) := stack[stack.size - 1]
    if isVisited visited cur parent then
      stack := stack.pop
    else if added then
      -- `visit`
      let mut vis := visited.getD ⟨cur⟩ 0
      let prereg := (← get).preregVisited.getD ⟨cur⟩ 0
      let ct := c.theoryOf cur
      let mut ths : Array Theory := #[ct]
      if cur != parent then
        let pt := c.theoryOf parent
        ths := ths.push pt
        match cur.typeHint with
        | some T => if ct != pt || isFiniteType T then ths := ths.push (typeTheory T)
        | none => pure ()
      for T in ths do
        if !hasTheory vis T then
          vis := vis ||| theoryBit T
          if !hasTheory prereg T then theoryPreRegister T cur
      visited := visited.insert ⟨cur⟩ vis
      setVisited cur (prereg ||| vis)
      if (vis ^^^ (vis &&& theoryBit ct)) != 0 then addSharedTerm atom cur vis
      stack := stack.pop
    else
      stack := stack.set! (stack.size - 1) (cur, parent, true)
      for ch in children cur do
        if !isVisited visited ch cur then stack := stack.push (ch, cur, false)

/-- `SharedSolver::preRegister`: with sharing, the visitor of shared terms, and
an equality is propagated by the shared terms database too (a trigger of the
central equality engine), unless it has a SAT value. -/
partial def preRegisterAtom (atom : Node) : EngineM Unit := do
  if !(← read).sharing then return ← preRegisterVisit atom
  sharedVisit atom
  if let .app (.kind .EQUAL) _ := atom then
    if (← read).eeSolver && !(← hasSatValue atom) then
      withEE (EE.addTriggerPredicate atom)

/-- `TheoryEngine::preRegister`, for an atom met by the CNF stream. -/
partial def preRegister (atom : Node) : EngineM Unit := do
  if (← get).registered.contains ⟨atom⟩ then return
  modify fun s => { s with registered := s.registered.insert ⟨atom⟩, registerLog := s.registerLog.push ⟨atom⟩ }
  if !isTheoryAtom (← read) atom then return
  emit (.prereg (← level) atom)
  addRoot atom
  preRegisterQueued atom

/-- `TheoryEngine::preRegister` of an atom that got a SAT literal, or again
after a backtrack (`TheoryPreregistrar`). -/
partial def tePreRegister (atom : Node) : EngineM Unit := do
  emit (.prereg (← level) atom)
  if atom.isConst then return
  if !(← get).registered.contains ⟨atom⟩ then
    modify fun s => { s with registered := s.registered.insert ⟨atom⟩ }
    addRoot atom
  preRegisterQueued atom

/-- The queue of `TheoryEngine::preRegister`. -/
partial def preRegisterQueued (atom : Node) : EngineM Unit := do
  modify fun s => { s with preregQueue := s.preregQueue.push atom }
  if (← get).inPrereg then return
  modify fun s => { s with inPrereg := true }
  repeat
    let q ← modifyGet fun s => (s.preregQueue, { s with preregQueue := #[] })
    if q.isEmpty then break
    -- the first first; those queued meanwhile after the rest
    let first := q[0]!
    modify fun s => { s with preregQueue := q.extract 1 q.size ++ s.preregQueue }
    preRegisterAtom first
  modify fun s => { s with inPrereg := false }

/-- `TheoryPreregistrar::notifySatLiteral` (eager): the atom is preregistered,
and remembered with the level. -/
partial def notifySatLiteral (atom : Node) : EngineM Unit := do
  -- the CNF stream creates the atom's negation with its literal (`newLiteral`)
  let o := (← read).order
  modify fun s => { s with ee := { s.ee with freshIds := o.numberFresh s.ee.freshIds (Node.notNode atom) } }
  -- (`TheoryPreregistrar::notifySatLiteral`: preregistered, then cached; the
  -- literals of a lemma its preregistration sends come first)
  tePreRegister atom
  modify fun s => { s with satLiterals := s.satLiterals.push (atom, s.level) }

/-- Give a lemma (rewritten, as cvc5's `TheoryPreprocessor` does), or the
negation of a conflict's explanation, to the CNF stream. -/
partial def satLemma (lem : Node) (isConflict : Bool) (kind : Option Pending) (proof : Option EqProof := none) :
    EngineM Unit := do
  let c ← read
  if isConflict then
    let conf := match lem with
      | .app (.kind .AND) cs => cs
      | l => #[l]
    let (exp, steps) ← explainAllSteps conf true true
    -- its certificate, from the literals of the clause only, and the literals
    -- the linear solver explained
    let ee := (← get).ee
    let ints := (steps.filter (·.arith)).map (·.lit)
    let lits := exp ++ ints
    let cert := match kind with
      | some (.constants a b) => (EE.conflictOfConstants ee lits lits a b).toOption
      | some (.dt cf) => (EE.conflictOfDt ee lits cf).toOption
      | some (.sets id conf) => (EE.conflictOfSets ee lits id conf).toOption
      | some (.strings id ps) => (EE.conflictOfStrings ee lits id ps).toOption
      | _ => none
    let src ← match kind with
      | some (.arith p) =>
        if steps.isEmpty then newSatSource (.arith (some (exp, p)))
        else
          -- the certificate refutes the conflict's literals, which the steps
          -- give from those of the clause
          let A := conf.filter (· != Node.mkTrue)
          newSatSource (.derived (#[(A.map negate, some (.arith A p))] ++ (← stepClauses exp steps)))
      | _ =>
        if ints.isEmpty then newSatSource (.theory cert)
        else
          let main := match cert with
            | some (A, q) => (A.map negate, some (.theory A q))
            | none => (lits.map negate, none)
          newSatSource (.derived (#[main] ++ (← stepClauses exp (steps.filter (·.arith)))))
    withCnf (Cnf.convertAndAssert (cnfHostWith notifySatLiteral c) (EE.mkAnd exp) false (negated := true) src)
    -- (`PropEngine::assertLemmasInternal` notifies the decision engine)
    modify fun s => { s with decisionQueue := s.decisionQueue.push (Node.notNode (EE.mkAnd exp)) }
  else
    let lem₀ := lem
    -- the lemma's nodes are created before its rewrite (cvc5's node ids)
    let lem := Telos.rewrite lem (← withEE (EE.numbered lem))
    let ids := (← get).ee.nodeIds
    let lem := if c.cvc5Order && !(match kind with | some .quant => true | _ => false) then
      orientEqs ids lem c.declOrder else lem
    -- the formula's proof, from the lemma's
    let src ← match kind with
      | some (.arith p) =>
        -- the clause's literals, whose negations the certificate refutes
        let lits := match lem with
          | .app (.kind .OR) cs => cs
          | l => #[l]
        let litsOf (l : Node) : Array Node := match l with
          | .app (.kind .OR) cs => cs
          | l => #[l]
        -- the certificate refutes the negations of the lemma's literals: as
        -- the clause has them, as the theory stated them, or as the theory
        -- rewrote them (in its order)
        let arithOrder := { c.arith.order with fresh := (← get).ee.freshIds }
        let cands := #[lits, litsOf lem₀, litsOf (Telos.rewrite lem₀ arithOrder)]
        let lits₀ := (cands.find? fun L => p.check (L.map negate)).getD lits
        if lits₀.all lits.contains then newSatSource (.arith (some (lits.map negate, p)))
        else
          -- each relates to one of the clause by its rewrite
          let rel := (lits₀.filter (!lits.contains ·)).map fun l₀ =>
            lits.findSome? fun l => rewriteClause l l₀
          let main := (lits₀, some (SatProof.Just.arith (lits₀.map negate) p))
          newSatSource (.derived (#[main] ++ (rel.filterMap id).map fun (d, j) => (d, some j)))
      | _ =>
        let cert := proof.bind (DtLemma.forFormula lem₀ lem) |>.map (lem, ·)
        newSatSource (.lemma cert)
    withCnf (Cnf.convertAndAssert (cnfHostWith notifySatLiteral c) lem false (src := src))
    modify fun s => { s with decisionQueue := s.decisionQueue.push lem }

/-- `TheoryEngine::lemma`, after the event: the lemma, preprocessed (rewritten),
goes to the CNF stream, which preregisters its new atoms. -/
partial def flushLemmas : EngineM Unit := do
  if (← read).satMode then
    repeat
      let q ← modifyGet fun s => (s.satLemmaQueue, { s with satLemmaQueue := #[] })
      if q.isEmpty then break
      for (lem, isConflict, kind, proof) in q do satLemma lem isConflict kind proof
    return
  repeat
    let q ← modifyGet fun s => (s.lemmaQueue, { s with lemmaQueue := #[] })
    if q.isEmpty then break
    for lem in q do
      -- cvc5's rewriter orients an equality by node ids, putting the newer
      -- term on the right: approximated by the order in which the equality
      -- engine met the terms (a term it does not have is the newest)
      for atom in formulaAtoms lem #[] do
        if !(← read).cvc5Order then
          preRegister atom
          continue
        let ids := (← get).ee.nodeIds
        let decl := (← read).declOrder
        let ord := (← read).order
        let atom := match atom with
          | .app (.kind .EQUAL) #[l, r] =>
            if l.typeHint == some .integer || l.typeHint == some .real then Telos.rewrite atom ord
            else if EE.ageLt ids r l decl then Node.eqNode r l else atom
          | _ => Telos.rewrite atom ord
        preRegister atom

end

/-- The engine as the CNF stream's host. -/
def cnfHost (c : Config) : Cnf.Host (StateT Cnf.State EngineM) := cnfHostWith notifySatLiteral c

/-- `TheoryPreregistrar::notifyBacktrack`: the atoms preregistered above the
current level are preregistered again, at it, the latest first. -/
def satBacktrack : EngineM Unit := do
  let lvl ← level
  let n := (← get).satLiterals.size
  for i in [0:n] do
    let (atom, l) := (← get).satLiterals[n - 1 - i]!
    if l ≤ lvl then break
    modify fun s => { s with satLiterals := s.satLiterals.set! (n - 1 - i) (atom, lvl) }
    tePreRegister atom

/-- The outputs of the linear solver from a literal it ensures on: the
literal gets its SAT literal (the CNF stream preregisters its atoms), a phase
is preferred (`OutputChannel::preferPhase`), and the rest as usual. -/
def flushArithDeferred : EngineM Unit := do
  let outs ← modifyGet fun s => (s.arithDeferred, { s with arithDeferred := #[] })
  let c ← read
  for o in outs do
    match o with
    | .ensureLiteral n => if c.satMode then withCnf (Cnf.ensureLiteral (cnfHost c) n)
    | .phase n pol =>
      emit (.phase (← level) n pol)
      if c.satMode then withCnf (Cnf.preferPhase n pol)
    | o => arithOutput o

/-- Run an operation of the equality engine, process its notes, and register
the atoms of the lemmas sent. -/
def withEEF (x : EE.EEM α) : EngineM α := do
  let a ← withEE x
  flushLemmas
  return a

/-- The theory of datatypes' `postCheck`, at the level of the engine: a lemma
of `checkSplit` is sent, and its atoms preregistered (which may process the
theory's pending facts), before the checks go on, as in cvc5. -/
def dtPostCheck (full : Bool) : EngineM Unit := do
  withEEF DT.process
  let conflict : EngineM Bool := do return (← get).inConflict || (← get).ee.teConflict
  let dt : EngineM DT.State := do return (← get).ee.dt
  -- (`Valuation::needCheck`: the output channel was used, or a lemma added, in
  -- this call of `check`)
  if !full || (← conflict) || (← dt).sentLemmas > 0 || (← get).outputUsed || (← get).lemmasAdded then
    return
  repeat
    withEEF (do DT.reset; DT.checkCycles; DT.process)
    if (← conflict) || (← dt).sentLemmas > 0 then return
    if (← dt).sentFacts == 0 then
      withEEF DT.reset
      let classes ← withEEF DT.classes
      for n in classes do
        if ← withEEF (DT.splitStep n) then break
      if (← dt).sentLemmas > 0 then withEEF (EE.modifyDt fun d => { d with pendingFacts := #[] })
      else withEEF DT.process
    let d ← dt
    if (← conflict) || d.sentLemmas > 0 || d.sentFacts == 0 then break

/-- The relevant terms of the theory of sets (`collectAssertedTerms`, with the
shared terms): the subterms of its facts, and its shared terms. -/
def setsRelevant : EngineM (Std.HashSet Key) := do
  let s ← get
  let rec go (acc : Std.HashSet Key) (t : Node) : Std.HashSet Key :=
    if acc.contains ⟨t⟩ then acc else
    let acc := acc.insert ⟨t⟩
    match t with
    | .app _ cs => cs.attach.foldl (fun acc ⟨c, _⟩ => go acc c) acc
    | _ => acc
  termination_by sizeOf t
  decreasing_by all_goals (simp_wf; have := Array.sizeOf_lt_of_mem ‹_›; omega)
  let acc := s.setsFacts.foldl (fun acc f => go acc (atomOf f).1) {}
  return s.setsShared.foldl (fun acc t => acc.insert ⟨t⟩) acc

/-- The theory of sets' `postCheck` at full effort, at the level of the engine:
each lemma is sent, and its atoms preregistered, as it is produced. -/
def setsPostCheck : EngineM Unit := do
  let relevant ← setsRelevant
  let ops : Sets.Ops EngineM := { run := fun x => withEEF x }
  Sets.postCheck ops relevant (do return (← get).outputUsed || (← get).lemmasAdded)

/-- The relevant terms of the theory of strings (`collectAssertedTerms`, with
the shared terms): the terms of its facts and shared terms, and their subterms
under the negations, equalities and terms of the theory (`collectTerms`). -/
def stringsRelevant : EngineM (Std.HashSet Key) := do
  let s ← get
  let rec go (acc : Std.HashSet Key) (t : Node) : Std.HashSet Key :=
    if acc.contains ⟨t⟩ then acc else
    let acc := acc.insert ⟨t⟩
    match t with
    | .app _ cs =>
      let k := t.getKind
      if k == .NOT || k == .EQUAL || Telos.theoryOf t == .THEORY_STRINGS then
        cs.attach.foldl (fun acc ⟨c, _⟩ => go acc c) acc
      else acc
    | _ => acc
  termination_by sizeOf t
  decreasing_by all_goals (simp_wf; have := Array.sizeOf_lt_of_mem ‹_›; omega)
  let acc := s.stringsFacts.foldl go {}
  return s.stringsShared.foldl go acc

/-- The theory of strings' `postCheck` (at every effort; the strategy at full
effort), at the level of the engine: each lemma is sent, and its atoms
preregistered, as it is produced. -/
def stringsPostCheck (full : Bool) : EngineM Unit := do
  let c ← read
  let relevant ← if full then stringsRelevant else pure {}
  let ops : Strings.Ops EngineM := {
    run := fun x => do let a ← withEE x; flushLemmas; pure a
    hasSatValue := hasSatValue
    phase := fun n pol => do
      emit (.phase (← level) n pol)
      if c.satMode then withCnf (Cnf.preferPhase n pol) }
  Strings.postCheck ops full relevant (do return (← get).outputUsed || (← get).lemmasAdded)

/-- `Theory::check` of one theory: for UF, its facts are asserted to the
equality engine, until the engine is in conflict. -/
def theoryCheck (T : Theory) (e : Effort) : EngineM Unit := do
  emit (.check (← level) T e)
  -- UF's check is the first of a round of checks: no lemma was sent in it yet
  if T == .THEORY_UF then withEEF (EE.modifyDt fun d => { d with lemmasAdded := false })
  if T == .THEORY_DATATYPES && (← read).dtSolver then
    withEEF DT.preCheck
    repeat
      let s ← get
      if s.inConflict || s.dtHead ≥ s.dtFacts.size then break
      let fact := s.dtFacts[s.dtHead]!
      modify fun s => { s with dtHead := s.dtHead + 1 }
      withEEF (DT.assertFact fact)
    dtPostCheck (e == .full)
  if T == .THEORY_STRINGS && (← read).stringsSolver then
    repeat
      let s ← get
      if s.inConflict || s.stringsHead ≥ s.stringsFacts.size then break
      let fact := s.stringsFacts[s.stringsHead]!
      modify fun s => { s with stringsHead := s.stringsHead + 1 }
      withEEF (Strings.assertFact fact)
    if !(← get).inConflict then stringsPostCheck (e == .full)
  if T == .THEORY_SETS && (← read).setsSolver then
    repeat
      let s ← get
      if s.inConflict || s.setsHead ≥ s.setsFacts.size then break
      let fact := s.setsFacts[s.setsHead]!
      modify fun s => { s with setsHead := s.setsHead + 1 }
      withEEF (Sets.assertFact fact)
    if e == .full && !(← get).inConflict then setsPostCheck
  if T == .THEORY_ARITH && (← read).arithSolver then
    -- `Theory::check`: `preCheck`, the facts (`preNotifyFact`), `postCheck`
    let newFacts := (← get).arithHead < (← get).arithFacts.size
    withArith (Arith.preCheck newFacts)
    repeat
      let s ← get
      if s.arithHead ≥ s.arithFacts.size then break
      let fact := s.arithFacts[s.arithHead]!
      modify fun s => { s with arithHead := s.arithHead + 1 }
      withArith (Arith.assertFact fact)
      -- a lemma (a disequality's split) goes to the CNF stream at once, which
      -- preregisters its atoms before the facts and the check go on
      flushLemmas
    let _ ← withArith (Arith.postCheck (e == .full))
    flushArithDeferred
    -- its lemmas go to the CNF stream before the next theory's check
    flushLemmas
  if T == .THEORY_QUANTIFIERS && (← read).quantSolver then
    repeat
      let s ← get
      if s.inConflict || s.quantHead ≥ s.quantFacts.size then break
      let fact := s.quantFacts[s.quantHead]!
      modify fun s => { s with quantHead := s.quantHead + 1 }
      let (atom, pol) := atomOf fact
      quantRun (Quant.assertQuantifier atom pol) flushLemmas
      flushLemmas
    if !(← get).inConflict then
      let st ← get
      quantRun (Quant.check e (st.outputUsed || st.lemmasAdded) #[]) flushLemmas
      flushLemmas
  if T == .THEORY_UF && (← read).eeSolver then
    repeat
      let s ← get
      if s.inConflict || s.ufHead ≥ s.ufFacts.size then break
      let fact := s.ufFacts[s.ufHead]!
      modify fun s => { s with ufHead := s.ufHead + 1 }
      withEEF (UF.assertFact fact)

/-! ## Theory combination (`CombinationCareGraph`) -/

/-- The equality engine's representative of a term. -/
def eeRep (ee : EE.EqualityEngine) (t : Node) : Node :=
  match ee.nodeIds.get? ⟨t⟩ with
  | some i => ee.nodes[EE.find ee i]!
  | none => t

/-- `getTriggerTermRepresentative`: the trigger term of the tag in the class
of `t`, if it is a trigger term of it (`isTriggerTerm`). -/
def eeTriggerRep? (ee : EE.EqualityEngine) (t : Node) (tag : Nat) : Option Node := do
  let i ← ee.nodeIds.get? ⟨t⟩
  let ts ← (ee.termTriggers[EE.find ee i]?).join
  if (EE.TSet.tags (some ts) >>> tag) % 2 == 1 then some ee.nodes[EE.TSet.get ts tag]! else none

def eeAreEqual (a b : Node) : EngineM Bool := return (← runEE (EE.areEqual a b)).1
def eeAreDisequal (a b : Node) : EngineM Bool := return (← runEE (EE.areDisequal a b false)).1

/-- `TheoryEngine::getEqualityStatus` (`SharedSolverDistributed`): by the
shared terms database (the central equality engine), for two shared terms;
otherwise by the theory of their type (arithmetic's model, or UF's equality
engine, which takes the others as disequal in the model). -/
def equalityStatus (a b : Node) : EngineM Arith.EqStatus := do
  let s ← get
  if s.notified.contains ⟨a⟩ && s.notified.contains ⟨b⟩ then
    if ← eeAreEqual a b then return .trueAndPropagated
    if ← eeAreDisequal a b then return .falseAndPropagated
  if (a.typeHint == some .real || a.typeHint == some .integer) && (← read).arithSolver then
    return ← withArith (Arith.equalityStatus a b)
  if ← eeAreEqual a b then return .isTrue
  if ← eeAreDisequal a b then return .isFalse
  return .falseInModel

/-- `areCareDisequal` of the theory `T`: disequal in the equality engine, or,
for two trigger terms of `T`, disequal by `getEqualityStatus` (UF's override
checks the disequality only for terms of the engine, which ours always are). -/
def areCareDisequal (T : Theory) (x y : Node) : EngineM Bool := do
  let ee := (← get).ee
  if ee.nodeIds.contains ⟨x⟩ && ee.nodeIds.contains ⟨y⟩ && (← eeAreDisequal x y) then return true
  match eeTriggerRep? ee x T.tag, eeTriggerRep? ee y T.tag with
  | some xs, some ys =>
    match ← equalityStatus xs ys with
    | .isFalse | .falseAndPropagated | .falseInModel => return true
    | _ => return false
  | _, _ => return false

/-- `CarePairArgumentCallback::considerPath`. -/
def considerPath (T : Theory) (a b : Node) : EngineM Bool := do
  if a == b then return true
  if a.isConst && b.isConst then return false
  return !(← areCareDisequal T a b)

/-- The care pairs of the theory `T` from its function terms, grouped by `key`
(`nodeTriePathPairProcess` on a trie per key): of the terms with a trigger
argument, one per vector of argument representatives (`TNodeTrie::addTerm`),
the pairs whose arguments may be equal (`considerPath`) give pairs of their
trigger arguments that are not equal (`processCarePairArgs`,
`addCarePairArgs`). The care graph is a set, so the order in which the pairs
are found does not matter. -/
def carePairsOf {κ : Type} [BEq κ] [Inhabited κ] (T : Theory) (terms : Array Node) (key : Node → Option κ) :
    EngineM (Array (Node × Node)) := do
  let tag := T.tag
  let ee := (← get).ee
  let mut groups : Array (κ × Array (Array Node × Node)) := #[]
  for app in terms do
    let (some k, .app _ cs) := (key app, app) | continue
    if !(cs.any fun c => (eeTriggerRep? ee c tag).isSome) then continue
    let reps := cs.map (eeRep ee)
    match groups.findIdx? (·.1 == k) with
    | some i =>
      if !(groups[i]!.2.any (·.1 == reps)) then
        groups := groups.modify i fun (k, es) => (k, es.push (reps, app))
    | none => groups := groups.push (k, #[(reps, app)])
  let mut out := #[]
  for (_, es) in groups do
    for i in [0:es.size] do
      for j in [i+1:es.size] do
        let (r1, fa) := es[i]!
        let (r2, fb) := es[j]!
        let mut ok := true
        for k in [0:r1.size] do
          if !(← considerPath T r1[k]! r2[k]!) then ok := false; break
        if !ok then continue
        -- `processCarePairArgs`
        if ← eeAreEqual fa fb then continue
        let ee := (← get).ee
        let (.app _ xs, .app _ ys) := (fa, fb) | continue
        for k in [0:xs.size] do
          let (x, y) := (xs[k]!, ys[k]!)
          if let (some xr, some yr) := (eeTriggerRep? ee x tag, eeTriggerRep? ee y tag) then
            if !(← eeAreEqual x y) then out := out.push (xr, yr)
  return out

/-- `TheoryUF::computeCareGraph`: its applications (registered), by function. -/
def ufCarePairs : EngineM (Array (Node × Node)) := do
  carePairsOf .THEORY_UF (← get).ufFunctionTerms fun
    | .app (.node .APPLY_UF f) _ => some f
    | _ => none

/-- `TheoryDatatypes::computeCareGraph`: its function terms (`d_functionTerms`,
the constructor applications with arguments and the selector applications, in
the order of their classes' creation: the order of the engine's nodes), by
operator and type (of the term for a constructor, of the argument for a
selector). -/
def dtCarePairs : EngineM (Array (Node × Node)) := do
  let ee := (← get).ee
  let mut terms := #[]
  for h : i in [0:ee.nodes.size] do
    if ee.isInternal[i]! then continue
    match ee.nodes[i] with
    | t@(.app (.node .APPLY_CONSTRUCTOR _) cs) => if cs.size > 0 then terms := terms.push t
    | t@(.app (.node .APPLY_SELECTOR _) _) => terms := terms.push t
    | _ => pure ()
  carePairsOf .THEORY_DATATYPES terms fun
    | t@(.app (.node .APPLY_CONSTRUCTOR f) _) => some (f, t.typeHint)
    | .app (.node .APPLY_SELECTOR f) #[x] => some (f, x.typeHint)
    | _ => none

/-- cvc5's node order, for the care pairs (`EE.ageLt`, with the order of the
declarations). -/
def idLt (c : Config) (ids : Std.HashMap Key Nat) (a b : Node) : Bool := EE.ageLt ids a b c.declOrder

/-- `CombinationCareGraph::combineTheories`: the care pairs of the parametric
theories (UF and datatypes: arithmetic is not parametric, its model only
prunes their pairs), a set ordered by theory and node
ids, each a split of the equality
(`COMBINATION_SPLIT`, by the builtin theory, whose lemmas are cached), whose
literal gets the preferred phase `true`. -/
def combineTheories : EngineM Unit := do
  let c ← read
  let mut pairs : Array (Nat × Node × Node) := #[]
  if c.eeSolver then
    for (a, b) in ← ufCarePairs do pairs := pairs.push (Theory.all.idxOf .THEORY_UF, a, b)
  if c.dtSolver then
    for (a, b) in ← dtCarePairs do pairs := pairs.push (Theory.all.idxOf .THEORY_DATATYPES, a, b)
  let ids := (← get).ee.nodeIds
  -- `CarePair`: the smaller node first; the set's order
  let normal := pairs.map fun (t, a, b) => if idLt c ids b a then (t, b, a) else (t, a, b)
  let lt := fun (x y : Nat × Node × Node) =>
    x.1 < y.1 || (x.1 == y.1 && (idLt c ids x.2.1 y.2.1 ||
      (x.2.1 == y.2.1 && idLt c ids x.2.2 y.2.2)))
  let sorted := normal.toList.mergeSort (fun x y => !lt y x)
  let mut seen : Array (Nat × Node × Node) := #[]
  for p in sorted do
    if seen.contains p then continue
    seen := seen.push p
    let (_, a, b) := p
    let eq := Node.eqNode a b
    let lem := Node.mkNode .OR #[eq, Node.notNode eq]
    let r := Telos.rewrite lem c.order
    if (← get).builtinLemmas.contains ⟨r⟩ then continue
    modify fun s => { s with builtinLemmas := s.builtinLemmas.insert ⟨r⟩, outputUsed := true, lemmasAdded := true }
    emit (.lemma (← level) .THEORY_BUILTIN "COMBINATION_SPLIT" lem)
    if c.satMode then
      -- (excluded middle: `split`)
      satLemma lem false none (some (.valid lem [DT.argStep .split eq]))
      -- `ensureLiteral`, and `PropEngine::preferPhase` (no event)
      let e := Telos.rewrite eq c.order
      let e := if c.cvc5Order then orientEqs ids e c.declOrder else e
      withCnf (Cnf.ensureLiteral (cnfHost c) e)
      withCnf (Cnf.preferPhase e true)

/-- `TheoryEngine::check`: rounds of checks of every enabled theory, while new
facts are asserted and there is no conflict. At full effort the first round
always runs. -/
def check (e : Effort) : EngineM Unit := do
  modify fun s => { s with outputUsed := false, lemmasAdded := false }
  if e == .full then modify fun s => { s with factsAsserted := true }
  repeat
    let s ← get
    if !s.factsAsserted || s.inConflict || s.lemmasAdded then break
    modify fun s => { s with factsAsserted := false }
    for T in (← read).theories do
      if T.hasCheck then
        theoryCheck T e
        if (← get).inConflict then break
    -- `TheoryEngine::propagate`: arithmetic's (the others propagate as they go)
    if !(← get).inConflict && (← read).arithSolver then withArith Arith.propagate
    -- at full effort, theory combination, if every fact was processed and no
    -- lemma was sent
    let st ← get
    if e == .full && (← read).sharing && !st.factsAsserted && !(st.outputUsed || st.lemmasAdded) &&
        !st.inConflict then
      combineTheories
  -- last call: the quantifiers engine (`QuantifiersEngine::check`), if the full
  -- check left nothing to do
  let st ← get
  if e == .full && (← read).quantSolver && !st.inConflict && !(st.outputUsed || st.lemmasAdded) then
    let ee := st.ee
    let mut all : Array Node := #[]
    for i in [0:ee.nodes.size] do
      if !ee.isInternal[i]! then all := all.push ee.nodes[i]!
    let all' := all
    quantRun (Quant.check .lastCall false all') flushLemmas
    flushLemmas

/-- The explanation of a propagated literal (`TheoryEngine::getExplanation`,
with the central equality engine), as its assumptions: the equality engine
explains it, and then, in turn, each assumption that the SAT solver did not
assert (the explanation of an internal fact), until all are; conjunctions are
split, and `true` dropped. -/
def explain (lit : Node) : EngineM (Array Node) := do
  if !(← read).eeSolver then return #[]
  explainAll #[lit] false

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
        -- the explanation, and the event, are left to `run`
        modify fun s => { s with pending := some (.prop lit) }
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
    let dtOn := (← read).dtSolver
    let setsOn := (← read).setsSolver
    modify fun s => { s with ee := { EE.init ctx with dt := { enabled := dtOn }, sets := { enabled := setsOn } } }
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
  -- a lemma needs the SAT solver, which `solve` does not have
  if s.lemmaSent then return .unknown
  if s.used.isEmpty || ((← read).ufSolver &&
      s.used.all ([.THEORY_UF, .THEORY_DATATYPES].contains ·)) then
    return .sat
  return .unknown

/-! ## Replay -/

/-- An input event of a cvc5 trace (`-o theory-events`): what the SAT solver
and the theory engine ask of the theories. -/
inductive Input where
  | prereg (level : Nat) (atom : Node)
  | assert (level : Nat) (T : Theory) (lit : Node)
  | check (level : Nat) (T : Theory) (e : Effort)
  | pop (level : Nat)
  /-- The SAT solver asks for the explanation of a propagated literal. -/
  | explain (level : Nat) (lit : Node)

/-- In a replay, the end of a call of `TheoryEngine::check`: the SAT solver
takes the literals propagated, and asserts those it had not assigned, unless
it is in conflict. With sharing this has effects even for those the theories
have already (shared equalities), whose assertion prints nothing. -/
def endCheckCall (flush : Bool) : EngineM Unit := do
  if !(← get).inCheckCall then return
  modify fun s => { s with inCheckCall := false }
  let lits ← modifyGet fun s => (s.propagated, { s with propagated := #[] })
  if !flush || (← get).inConflict then return
  modify fun s => { s with pendingProps := s.pendingProps ++ lits }

/-- The SAT solver asserts the first `upto` pending propagated literals (or
all): those the trace does not show (the theories have them already) are
asserted before the next one it shows. -/
def assertPending (upto : Option Nat := none) : EngineM Unit := do
  let ps ← modifyGet fun s => (s.pendingProps, { s with pendingProps := #[] })
  let n := upto.getD ps.size
  for lit in ps.extract 0 n do
    if !(← get).assignment.contains ⟨(atomOf lit).1⟩ then assign lit
  modify fun s => { s with pendingProps := ps.extract n ps.size ++ s.pendingProps }

/-- Replay one input. -/
def replayInput : Input → EngineM Unit
  | .prereg k atom => do
    if k == 0 then
      -- `true` and `false`, at the solver's initialization
      emit (.prereg 0 atom)
    else
      raiseTo k
      -- telos may have registered it already, as the atom of a lemma
      if !(← get).registered.contains ⟨atom⟩ then
        emit (.prereg k atom)
        modify fun s => { s with registered := s.registered.insert ⟨atom⟩, registerLog := s.registerLog.push ⟨atom⟩ }
        addRoot atom
        preRegisterAtom atom
  | .assert k T lit => do
    endCheckCall true
    -- the SAT solver asserts its propagated literals in order, each followed by
    -- its Boolean propagation (the trace's other asserts)
    if let some i := (← get).pendingProps.findIdx? (· == lit) then assertPending (some (i + 1))
    raiseTo k
    -- a literal of the SAT solver, or a shared equality from the shared solver,
    -- to the theory that asked for it
    let marked := (← get).markedBuiltin
    if marked.contains ⟨lit⟩ || marked.contains ⟨flipEq lit⟩ then
      -- telos gave it to the theory already (a shared equality); the SAT
      -- solver may still assign it
      if (← get).registered.contains ⟨(atomOf lit).1⟩ && T == (← read).theoryOf (atomOf lit).1 then
        let (atom, pol) := atomOf lit
        if !(← get).assignment.contains ⟨atom⟩ then
          modify fun s => { s with assignment := s.assignment.insert ⟨atom⟩ pol,
                                   assignTrail := s.assignTrail.push ⟨atom⟩,
                                   asserted := s.asserted.push lit }
    else if (← get).registered.contains ⟨(atomOf lit).1⟩ && T == (← read).theoryOf (atomOf lit).1 then
      assign lit
    else assertFact lit false (some T)
  | .check k T e => do
    raiseTo k
    let ths := (← read).theories.filter (·.hasCheck)
    if some T == ths.head? then
      -- a new round of checks; it continues the call if facts were asserted in
      -- the last round, with no conflict and no lemma (`TheoryEngine::check`)
      let s ← get
      let continues := s.inCheckCall && s.lastWasLast && s.factsAsserted && !s.inConflict &&
        !s.ee.dt.lemmasAdded
      if !continues then
        endCheckCall true
        assertPending
      modify fun s => { s with inCheckCall := true, factsAsserted := false }
    theoryCheck T e
    modify fun s => { s with lastWasLast := some T == ths.getLast? }
  | .pop k => do
    endCheckCall false
    modify fun s => { s with pendingProps := #[] }
    popTo k
    emit (.pop k)
  | .explain k lit => do
    endCheckCall false
    raiseTo k
    -- the verified explanation, with the roots the asserted literals
    match EE.explainLitV (← exCtx) lit with
    | some exp => emit (.explain k lit (EE.mkAnd exp))
    | none =>
      modify fun s => { s with unverifiedExplains := s.unverifiedExplains + 1 }
      emit (.explain k lit (EE.mkAnd (← explain lit)))

/-- **Replay** a cvc5 trace: give the theories the inputs that cvc5's SAT
solver and theory engine gave its theories, in order, and record telos's
events. The SAT solver's decisions and backtracking come from the trace, so
the theories are compared with cvc5's on inputs with SAT structure, without a
SAT solver. -/
def replay (c : Config) (inputs : List Input) : Array Event × Nat :=
  let c := { c with replaying := true }
  let act : EngineM Unit := do
    if c.ufSolver then
      let ctx ← eeCtx
      modify fun s => { s with ee := { EE.init ctx with dt := { enabled := c.dtSolver }, sets := { enabled := c.setsSolver }, strings := { enabled := c.stringsSolver } } }
    for i in inputs do replayInput i
  let st := ((act.run c).run {}).2
  (st.events, st.unverifiedExplains)

/-- The result of the engine. -/
structure Result where
  answer : Answer
  events : Array Event
  /-- Why an `unsat` of the engine was not certified, and so answered
  `unknown`. -/
  uncertified : Option String := none
  /-- The certificate of an `unsat` answer. -/
  cert : Option (Array Node × EqProof) := none
  /-- The `unsat` was certified by a certificate, not by the verified
  explanation. -/
  byCertificate : Bool := false
  /-- For a `sat` answer: the equality engine and the literals asserted, from
  which the model is built (`buildModel`). -/
  ee : EE.EqualityEngine := default
  asserted : Array Node := #[]
  /-- The model of a certified `sat` answer. -/
  model : Option Model := none
  /-- For a `sat` answer: the arithmetic solver's values of its variables
  (`collectModelValues`). -/
  arithModel : Array (Node × Rat) := #[]
  /-- The certificate of an `unsat` answer of the SAT solver: the input
  formulas and the refutation (`Telos/Solver/SatProof.lean`). -/
  satCert : Option (Array Node × SatProof.Cert) := none

/-- The certificate `(A, p)` refutes the literals `lits`: `p` proves
`(true, false)` from the closed assumptions `A`, all of which are among
`lits`. -/
def certifies (lits : List Node) (A : Array Node) (p : EqProof) : Bool :=
  A.all (fun l => lits.any (fun x => decide (x = l))) && EqProof.checkConflict A p

/-- **Certify a conflict** with the verified explanations
(`Telos/Solver/Explain.lean`): its explanation, if the reasons are among the
literals `lits` (which are the roots, for the typing of applications) and
closed, and, for a propagation, the negation of the literal is among them too.
(`verification/TelosProofs/Solver/Solve.lean`: then no well-formed model
satisfies `lits`.) -/
def certifyV (lits : List Node) (ee : EE.EqualityEngine) : Pending → Option (Array Node)
  | .prop lit =>
    let roots := lits.toArray
    let C : EE.ExCtx := { ee, roots, paths := EE.subtermPaths roots }
    match EE.explainLitV C lit with
    | some exp =>
      if exp.all (fun l => lits.any (fun x => decide (x = l))) &&
          lits.any (fun x => decide (x = negate lit)) && EqProof.closedAssumptions exp then some exp
      else none
    | none => none
  | .constants a b =>
    let roots := lits.toArray
    let C : EE.ExCtx := { ee, roots, paths := EE.subtermPaths roots }
    match ee.nodeIds.get? ⟨a⟩, ee.nodeIds.get? ⟨b⟩ with
    | some i, some j =>
      if C.node i == a && C.node j == b &&
          ((a == Node.mkTrue && b == Node.mkFalse) || (a == Node.mkFalse && b == Node.mkTrue)) then
        match EE.runFull C i j with
        | some exp =>
          if exp.all (fun l => lits.any (fun x => decide (x = l))) && EqProof.closedAssumptions exp then
            some exp
          else none
        | none => none
      else none
    | _, _ => none
  | .dt _ | .arith _ | .sets .. | .strings .. => none
  | .quant => none

/-- The explanation of a pending conflict by the equality engine's own
explanation (`EE.explainLit`, not verified), and the certificate of the
conflict (`EqProof`), for when the verified explanation does not apply, and for
the CPC proof. -/
def explainPending (s : State) : Pending → Array Node × Except String (Array Node × EqProof)
  | .prop lit =>
    let exp := ((EE.explainLit lit).run { congruenceKinds := UF.congruenceKind, value := fun _ => none }
      |>.run s.ee).1
    (exp, EE.conflictOfPropagation s.ee s.asserted exp lit (negate lit))
  | .constants a b =>
    let exp := ((EE.explainLit (Node.eqNode a b)).run { congruenceKinds := UF.congruenceKind, value := fun _ => none }
      |>.run s.ee).1
    (exp, EE.conflictOfConstants s.ee s.asserted exp a b)
  | .dt cf => (#[], EE.conflictOfDt s.ee s.asserted cf)
  | .arith _ => (#[], .error "a conflict of linear arithmetic, outside the SAT solver")
  | .sets id conf => (#[], EE.conflictOfSets s.ee s.asserted id conf)
  | .strings id ps => (#[], EE.conflictOfStrings s.ee s.asserted id ps)
  | .quant => (#[], .error "a lemma of the quantifiers engine is not a conflict")

/-- The event of a pending conflict, with its explanation. -/
def Pending.event (k : Nat) (exp : Array Node) : Pending → Event
  | .prop lit => .explain k lit (EE.mkAnd exp)
  | .constants _ _ => .conflict k .THEORY_BUILTIN "EQ_CONSTANT_MERGE" (EE.mkAnd exp)
  | .dt cf => .conflict k .THEORY_DATATYPES cf.id (EE.mkAnd exp)
  | .arith _ => .conflict k .THEORY_ARITH "" (EE.mkAnd exp)
  | .sets id _ => .conflict k .THEORY_SETS id (EE.mkAnd exp)
  | .strings id _ => .conflict k .THEORY_STRINGS id (EE.mkAnd exp)
  | .quant => .conflict k .THEORY_QUANTIFIERS "" (EE.mkAnd exp)

/-- Run `solve` on `lits`. An `unsat` answer stands only if it is certified:
by the verified explanation of its conflict (`certifyV`), or else by a
certificate that refutes `lits` (`certifies`); it is `unknown` otherwise. The
explanation of the conflict, the last event, is computed here. -/
def run (c : Config) (lits : List Node) : Result :=
  let c := { c with defer := true }
  let (a, s) := ((solve lits).run c).run {}
  if a != .unsat then { answer := a, events := s.events, ee := s.ee, asserted := s.asserted } else
  match s.pending with
  | some p =>
    match certifyV lits s.ee p with
    | some exp =>
      let events := s.events.push (p.event s.level exp)
      let cert := if c.wantProof then
        match (explainPending s p).2 with
        | .ok (A, q) => if certifies lits A q then some (A, q) else none
        | .error _ => none
        else none
      { answer := .unsat, events, cert }
    | none =>
      let (exp, cert) := explainPending s p
      -- a conflict of a theory has its event already
      let events := match p with
        | .dt _ => s.events
        | _ => s.events.push (p.event s.level exp)
      match cert with
      | .error e => { answer := .unknown, events, uncertified := some e }
      | .ok (A, q) =>
        if certifies lits A q then { answer := .unsat, events, cert := some (A, q), byCertificate := true }
        else { answer := .unknown, events, uncertified := some "the certificate does not check" }
  | none =>
    match s.cert with
    | .error e => { answer := .unknown, events := s.events, uncertified := some e }
    | .ok (A, q) =>
      if certifies lits A q then { answer := .unsat, events := s.events, cert := some (A, q) }
      else { answer := .unknown, events := s.events, uncertified := some "the certificate does not check" }

/-- **An `unsat` answer is certified**: by the verified explanation of a
conflict, or by a certificate that refutes the literals.
(`verification/TelosProofs/Solver/Solve.lean` turns this into: no well-formed
model satisfies the literals.) -/
theorem run_unsat (c : Config) (lits : List Node) (h : (run c lits).answer = .unsat) :
    (∃ ee p exp, certifyV lits ee p = some exp) ∨ ∃ A q, certifies lits A q = true := by
  unfold run at h
  dsimp only at h
  split at h
  split at h
  · simp_all
  · split at h
    · rename_i p _
      split at h
      · rename_i exp hexp
        exact .inl ⟨_, p, exp, hexp⟩
      · split at h
        · simp at h
        · rename_i A q _
          split at h
          · exact .inr ⟨A, q, by assumption⟩
          · simp at h
    · split at h
      · simp at h
      · rename_i A q _
        split at h
        · exact .inr ⟨A, q, by assumption⟩
        · simp at h

end Telos.Solver
