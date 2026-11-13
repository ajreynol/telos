import TelosProofs.Driver

/-!
# Correctness of the rewriter

The central theorem: rewriting a well-typed node yields an equivalent node. The
rewriter's result is certified, so it follows from `Certified.equiv`. The
statement is final and stays fixed as theory rewriters are added.
-/

namespace Telos

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  rewriteWith_sound theoryRewriter defaultFuel t h

end Telos
