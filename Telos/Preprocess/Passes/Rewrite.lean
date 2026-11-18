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

/-- Rewrite every assertion. -/
def Pipeline.rewrite {input : Node} (p : Pipeline input) : Pipeline input :=
  if Pipeline.inConflict p then p
  else
    match h : p.1 with
    | .app (.kind .AND) cs =>
      let r : Rw (.app (.kind .AND) cs) := Rw.congr (.kind .AND) cs rewriteCert rfl (.inl rfl)
      Pipeline.conflict? (p.trans (h ▸ r))
    | _ => p

end Telos.Preprocess
