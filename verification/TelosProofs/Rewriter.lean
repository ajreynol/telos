import TelosProofs.Driver

/-!
# Correctness of the rewriter

The central theorem: rewriting a well-typed node yields an equivalent node. It
follows from the driver's correctness and the correctness of each theory
rewriter. The statement is final and stays fixed as theory rewriters are added.
-/

namespace Telos

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  rewriteWith_sound theoryRewriter_correct defaultFuel t h

end Telos
