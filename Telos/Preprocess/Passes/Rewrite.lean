import Telos.Preprocess.Pipeline
import Telos.Rewriter.Rewrite

/-!
# The `rewrite` pass

cvc5's `Rewrite` pass (`src/preprocessing/passes/rewrite.cpp`): each assertion is
replaced by its rewrite (telos's rewriter, `rewriteCert`). Certified by
congruence below the conjunction. As `AssertionPipeline::replace`, an assertion
that rewrites to `false` is a conflict, and a conjunction is not split again.
-/

namespace Telos.Preprocess

/-- Rewrite every assertion, with the order of node ids `o`. -/
def Pipeline.rewrite {input : Node} (p : Pipeline input) (o : NodeOrder := {}) : Pipeline input :=
  Pipeline.mapAssertions p (rewriteCert · o)

end Telos.Preprocess
