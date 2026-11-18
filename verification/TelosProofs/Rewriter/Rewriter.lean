import TelosProofs.Rewriter.Driver

/-!
# Correctness of the rewriter

The central theorem: rewriting a well-typed node yields an equivalent node. The
rewriter's result is certified, so it follows from `Certified.equiv`. The
statement is final and stays fixed as theory rewriters are added.

It is proved here from the Logos theorems it uses (`LogosFacts`), taken as a
hypothesis so that this build does not need Logos's proofs.
`Telos.rewrite_correct` (`TelosFull/Main.lean`) discharges it with Logos's
proofs.
-/

namespace Telos

/-- **Correctness of the rewriter**, given the Logos theorems it uses
(`LogosFacts`). Rewriting a well-typed node gives an equivalent node. -/
theorem rewrite_correct_of_logos [LogosFacts] (t : Node) (h : t.WellTyped) :
    t.Equiv (rewrite t) :=
  rewriteWith_sound theoryRewriter defaultFuel t h

end Telos
