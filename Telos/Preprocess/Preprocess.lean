import Telos.Preprocess.Passes.Rewrite
import Telos.Preprocess.Passes.StaticRewrite
import Telos.Preprocess.Passes.TheoryPreprocess
import Telos.Preprocess.Passes.NonClausalSimp

/-!
# The preprocessor

A port of cvc5's `ProcessAssertions::apply` (`src/smt/process_assertions.cpp`):
the preprocessing passes, in cvc5's order, on the pipeline of the input
assertions. The plan is `docs/preprocessor-plan.md`.

Ported so far: the pipeline (`Pipeline.init`, which splits conjunctions), the
`rewrite` pass, `static-rewrite` in part, and `theory-preprocess` with term
formula removal and the `ppRewrite` of arithmetic, bit-vectors and datatypes. This matches cvc5 with the
passes that are not ported switched off (`--simplification=none
--no-static-learning`), up to the order cvc5 takes from node ids. `apply-substs` has
nothing to do: `define-fun`s are expanded when the script is read.

Every result is equivalent to the input: the pipeline is a certified rewrite of
the conjunction `inputNode as` of the input assertions and `true`
(`Telos.preprocess_correct`).
-/

namespace Telos.Preprocess

/-- cvc5's `ProcessAssertions::apply`, on the assertions `as`. -/
def preprocessCert (as : List Node) (simplify : Bool := true) : Pipeline (inputNode as) :=
  let pass {α : Type} (name : String) (f : Unit → α) : α := Profile.time "pass" (fun _ => name) f
  let p := pass "init" fun _ => Pipeline.init as
  let p := pass "rewrite" fun _ => Pipeline.rewrite p
  -- `simplifyAssertions`: non-clausal simplification (`static-learning`, which
  -- follows, is not ported)
  let p := if simplify then pass "non-clausal-simp" fun _ => Pipeline.nonClausalSimp p else p
  let p := pass "rewrite (2)" fun _ => Pipeline.rewrite p
  let p := pass "static-rewrite" fun _ => Pipeline.staticRewrite p
  pass "theory-preprocess" fun _ => Pipeline.theoryPreprocess p

/-- The preprocessed assertions, and the definitions of the solved variables. -/
def preprocess (as : List Node) (simplify : Bool := true) : Array Node × List Node :=
  let p := preprocessCert as simplify
  (Pipeline.assertions p, Pipeline.defs p)

end Telos.Preprocess
