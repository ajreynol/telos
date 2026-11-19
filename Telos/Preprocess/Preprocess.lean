import Telos.Preprocess.Passes.Rewrite
import Telos.Preprocess.Passes.StaticRewrite
import Telos.Preprocess.Passes.TheoryPreprocess
import Telos.Preprocess.Passes.NonClausalSimp
import Telos.Preprocess.Passes.StaticLearning

/-!
# The preprocessor

A port of cvc5's `ProcessAssertions::apply` (`src/smt/process_assertions.cpp`):
the preprocessing passes, in cvc5's order, on the pipeline of the input
assertions. The plan is `docs/preprocessor-plan.md`.

Ported: the pipeline (`Pipeline.init`, which splits conjunctions), `rewrite`,
`non-clausal-simp` (twice with `--repeat-simp`, as `simplifyAssertions` does, and
again after static learning), `static-learning`, `static-rewrite` in part, and
`theory-preprocess` with term formula removal and the `ppRewrite` of arithmetic,
bit-vectors, datatypes and strings. The options are cvc5's, with the defaults of
the logic (`Telos/Preprocess/Options.lean`). `apply-substs` has nothing to do:
`define-fun`s are expanded when the script is read.

Every result is equivalent to the input: the pipeline is a certified rewrite of
the conjunction `inputNode as` of the input assertions and `true`
(`Telos.preprocess_correct`).
-/

namespace Telos.Preprocess

/-- cvc5's `ProcessAssertions::apply`, on the assertions `as`. -/
def preprocessCert (as : List Node) (opts : PPOptions := {}) : Pipeline (inputNode as) :=
  let pass {α : Type} (name : String) (f : Unit → α) : α := Profile.time "pass" (fun _ => name) f
  let p := pass "init" fun _ => Pipeline.init as
  let p := pass "rewrite" fun _ => Pipeline.rewrite p
  -- `simplifyAssertions`: non-clausal simplification, twice with `repeat-simp`
  let simplifyAssertions (p : Pipeline (inputNode as)) : Pipeline (inputNode as) × Array Node :=
    if !opts.simplification then (p, #[]) else
    let (p, lits) := pass "non-clausal-simp" fun _ => Pipeline.nonClausalSimpB p opts.termBased
    if !opts.repeatSimp then (p, lits) else
    let (p, lits') := pass "non-clausal-simp" fun _ => Pipeline.nonClausalSimpB p opts.termBased
    (p, lits ++ lits')
  let (p, lits) := simplifyAssertions p
  let p := if opts.staticLearning then
      pass "static-learning" fun _ => Pipeline.staticLearning p opts lits else p
  let p := if opts.repeatSimp then (simplifyAssertions p).1 else p
  let p := pass "rewrite (2)" fun _ => Pipeline.rewrite p
  let p := pass "static-rewrite" fun _ => Pipeline.staticRewrite p opts
  pass "theory-preprocess" fun _ => Pipeline.theoryPreprocess p

/-- The preprocessed assertions, and the definitions of the solved variables. -/
def preprocess (as : List Node) (opts : PPOptions := {}) : Array Node × List Node :=
  let p := preprocessCert as opts
  (Pipeline.assertions p, Pipeline.defs p)

end Telos.Preprocess
