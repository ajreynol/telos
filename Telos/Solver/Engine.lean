import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Preprocess.Options
import Telos.Solver.Event

/-!
# The theory engine, on conjunctions of literals

A port of cvc5's `TheoryEngine` (`src/theory/theory_engine.cpp`) for inputs with
no SAT structure: the preprocessed assertions are literals, which are asserted
one at a time, as cvc5's SAT solver does with unit clauses. A small stand-in
for the SAT solver (`Assignment`) keeps the values of the literals.

What cvc5 does on such inputs, observed with `-o theory-events`
(`docs/theory-engine-plan.md`, "Stage 1"):

1. it preregisters `true` and `false` at level 0;
2. it preregisters each atom, in assertion order, at level 1;
3. it asserts each literal, in order, to the theory of its atom;
4. it runs the theory engine's `check` at standard effort, then at full effort:
   each runs every enabled theory's `check`, in cvc5's order, until no new
   facts are asserted.

The engine records each event (`Event`), for comparison with cvc5's trace.
There are no theory solvers yet: every theory's `check` does nothing. So the
answer is `sat` only when no theory was given a literal, and `unknown`
otherwise.
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

/-- The theory that owns an atom (`Theory::theoryOf`). -/
def Config.theoryOf (c : Config) (atom : Node) : Theory :=
  Theory.ofTheoryId (Preprocess.ppTheoryOf c.termBased atom)

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

structure State where
  events : Array Event := #[]
  /-- The SAT context level. -/
  level : Nat := 0
  assignment : Assignment := {}
  /-- The atoms preregistered so far. -/
  registered : Std.HashSet Key := {}
  /-- Facts were asserted to a theory since the last round of checks
  (`TheoryEngine::d_factsAsserted`). -/
  factsAsserted : Bool := false
  inConflict : Bool := false
  /-- The theories that were given a literal. -/
  used : Array Theory := #[]

abbrev EngineM := ReaderT Config (StateM State)

def emit (e : Event) : EngineM Unit :=
  modify fun s => { s with events := s.events.push e }

/-- The atom and polarity of a literal. -/
def atomOf (lit : Node) : Node × Bool :=
  match lit with
  | .app (.kind .NOT) #[a] => (a, false)
  | _ => (lit, true)

/-- Whether an atom is a theory atom, given to a theory solver, rather than a
Boolean variable, which only the SAT solver sees. -/
def isTheoryAtom (c : Config) (atom : Node) : Bool :=
  c.theoryOf atom != .THEORY_BOOL

/-- `TheoryEngine::preRegister`, for an atom met by the CNF stream. -/
def preRegister (atom : Node) : EngineM Unit := do
  if (← get).registered.contains ⟨atom⟩ then return
  modify fun s => { s with registered := s.registered.insert ⟨atom⟩ }
  if !isTheoryAtom (← read) atom then return
  emit (.prereg (← get).level atom)

/-- `Theory::assertFact`, via `TheoryEngine::assertFact`: the literal is given
to the theory of its atom. -/
def assertFact (lit : Node) : EngineM Unit := do
  let (atom, _) := atomOf lit
  let c ← read
  if !isTheoryAtom c atom then return
  let T := c.theoryOf atom
  emit (.assert (← get).level T lit)
  modify fun s => { s with factsAsserted := true,
                           used := if s.used.contains T then s.used else s.used.push T }

/-- The SAT solver assigns `lit` (a unit, or a propagated literal). Returns
false on a propositional conflict: `lit` is already false. -/
def assign (lit : Node) : EngineM Bool := do
  let (atom, pol) := atomOf lit
  match (← get).assignment.get? ⟨atom⟩ with
  | some v => return v == pol
  | none =>
    modify fun s => { s with assignment := s.assignment.insert ⟨atom⟩ pol }
    assertFact lit
    return true

/-- `Theory::check` of one theory. -/
def theoryCheck (T : Theory) (e : Effort) : EngineM Unit := do
  emit (.check (← get).level T e)

/-- `TheoryEngine::check`: rounds of checks of every enabled theory, while new
facts are asserted and there is no conflict. At full effort the first round
always runs. -/
def check (e : Effort) : EngineM Unit := do
  if e == .full then modify fun s => { s with factsAsserted := true }
  -- each round asserts no new facts yet, so the loop runs at most once
  if (← get).factsAsserted && !(← get).inConflict then
    modify fun s => { s with factsAsserted := false }
    for T in (← read).theories do
      if T.hasCheck then
        theoryCheck T e
        if (← get).inConflict then break

/-- Solve the conjunction of the literals `lits`, as cvc5's SAT solver does
with unit clauses: register their atoms, assert them, then check at standard
and at full effort. -/
def solve (lits : List Node) : EngineM Answer := do
  emit (.prereg 0 Node.mkTrue)
  emit (.prereg 0 Node.mkFalse)
  modify fun s => { s with registered := (s.registered.insert ⟨Node.mkTrue⟩).insert ⟨Node.mkFalse⟩ }
  if lits.contains Node.mkFalse then return .unsat
  modify fun s => { s with level := 1 }
  for l in lits do preRegister (atomOf l).1
  for l in lits do
    if !(← assign l) then return .unsat
  check .standard
  if (← get).inConflict then return .unsat
  check .full
  if (← get).inConflict then return .unsat
  -- no theory solver is implemented yet: `sat` only if no theory has a literal
  return if (← get).used.isEmpty then .sat else .unknown

/-- Run `solve` on `lits`: the answer and the events. -/
def run (c : Config) (lits : List Node) : Answer × Array Event :=
  let (a, s) := ((solve lits).run c).run {}
  (a, s.events)

end Telos.Solver
