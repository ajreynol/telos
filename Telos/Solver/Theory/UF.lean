import Telos.Core.Node.FastType
import Telos.Solver.EqualityEngine

/-!
# The theory of uninterpreted functions

A port of cvc5's `TheoryUF` (`src/theory/uf/theory_uf.cpp`) with the central
equality engine (`--ee-mode=central`), in the configuration of safe mode: no
cardinality constraints, no higher order, no symmetry breaking. With the
central equality engine, UF only registers its terms and asserts its facts to
it: the engine's propagations and conflicts are those of the central engine,
which cvc5 reports as `THEORY_BUILTIN`'s (`EqEngineManagerCentral`).
-/

namespace Telos.Solver.UF

open EE

/-- `TheoryState::addEqualityEngineTriggerPredicate`: a trigger for the
predicate's value, unless it already has a SAT value. -/
def addTriggerPredicate (p : Node) : EEM Unit := do
  if ((← read).value p).isNone then EE.addTriggerPredicate p else addTerm p

/-- `TheoryUF::preRegisterTerm`. -/
def preRegisterTerm (n : Node) : EEM Unit :=
  match n with
  | .app (.kind .EQUAL) _ => addTriggerPredicate n
  | .app (.node .APPLY_UF _) _ =>
    if n.typeHint == some .boolean then addTriggerPredicate n else addTerm n
  | _ => addTerm n

/-- `Theory::check`'s processing of one fact: asserted to the equality engine,
with the fact as its reason. -/
def assertFact (fact : Node) : EEM Unit := do
  let (atom, pol) := match fact with
    | .app (.kind .NOT) #[a] => (a, false)
    | _ => (fact, true)
  match atom with
  | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol fact
  | _ => let _ ← assertPredicate atom pol fact

/-- The kinds UF adds to the equality engine (`TheoryUF::finishInit`; the
bit-vector conversions are outside telos's scope). -/
def congruenceKind (k : Kind) : Bool := k == .APPLY_UF

end Telos.Solver.UF
