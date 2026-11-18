import Telos.Preprocess.Passes.Rewrite
import Telos.Preprocess.Passes.StaticRewrite

/-!
# The preprocessor

A port of cvc5's `ProcessAssertions::apply` (`src/smt/process_assertions.cpp`):
the preprocessing passes, in cvc5's order, on the pipeline of the input
assertions. The plan is `docs/preprocessor-plan.md`.

Ported so far: the pipeline (`Pipeline.init`, which splits conjunctions), the
`rewrite` pass, `static-rewrite` in part, and of `theory-preprocess` only the
rewriting of the assertions. This matches cvc5 with the passes that are not ported switched
off (`--simplification=none --no-static-learning`), on assertions that
`theory-preprocess` and `static-rewrite` do not change. `apply-substs` has
nothing to do: `define-fun`s are expanded when the script is read.

Every result is equivalent to the input: the pipeline is a certified rewrite of
the conjunction `inputNode as` of the input assertions and `true`
(`Telos.preprocess_correct`).
-/

namespace Telos.Preprocess

/-- cvc5's `ProcessAssertions::apply`, on the assertions `as`. -/
def preprocessCert (as : List Node) : Pipeline (inputNode as) :=
  let p := Pipeline.init as
  -- `rewrite`: assertions must be rewritten here (cvc5 rewrites again before
  -- `static-rewrite`, which changes nothing).
  let p := Pipeline.rewrite p
  let p := Pipeline.staticRewrite p
  -- `theory-preprocess`, so far only its rewriting of each assertion.
  Pipeline.rewrite p

/-- The preprocessed assertions. -/
def preprocess (as : List Node) : Array Node := Pipeline.assertions (preprocessCert as)

end Telos.Preprocess
