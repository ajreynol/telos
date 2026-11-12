import Telos.Node.Node

/-!
# Rewriter

Modelled on cvc5's `Rewriter` (`src/theory/rewriter.h`) and `TheoryRewriter`
(`src/theory/theory_rewriter.h`). Each theory supplies `preRewrite` and
`postRewrite`, which return a `RewriteResponse`. A generic driver applies them to
a fixpoint, dispatching on `Kind.theoryId`.

The driver is a **stub** for now: `rewrite` is the identity. Its correctness
theorem, `Telos.rewrite_correct` in `verification/TelosProofs/Rewriter.lean`, is
already stated in its final form.

The driver will take fuel and return its input when the fuel runs out. That stays
sound because the identity is an equivalence, and it avoids `partial def`, which
proofs cannot see through.
-/

namespace Telos

/-- cvc5's `RewriteStatus`. -/
inductive RewriteStatus where
  /-- The node is in normal form for this theory. -/
  | REWRITE_DONE
  /-- Rewrite the result again at the top level. -/
  | REWRITE_AGAIN
  /-- Rewrite the result again, including its children. -/
  | REWRITE_AGAIN_FULL
  deriving DecidableEq, Repr, Inhabited

/-- cvc5's `RewriteResponse`. -/
structure RewriteResponse where
  status : RewriteStatus
  node : Node
  deriving Inhabited

/-- cvc5's `TheoryRewriter` interface. -/
structure TheoryRewriter where
  preRewrite : Node → RewriteResponse
  postRewrite : Node → RewriteResponse

namespace TheoryRewriter

/-- A theory rewriter that leaves every node unchanged. -/
def trivial : TheoryRewriter where
  preRewrite n := ⟨.REWRITE_DONE, n⟩
  postRewrite n := ⟨.REWRITE_DONE, n⟩

end TheoryRewriter

/-- cvc5's `Rewriter::rewrite`: rewrite a node to its normal form.
Stub: the identity, until the driver and theory rewriters exist. -/
def rewrite (t : Node) : Node := t

end Telos
