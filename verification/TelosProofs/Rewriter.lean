import TelosProofs.Driver

/-!
# Correctness of the rewriter

The central theorem: rewriting a well-typed node yields an equivalent node. The
rewriter's result is certified, so it follows from `Certified.equiv`. The
statement is final and stays fixed as theory rewriters are added.

It is proved here from Logos's checker soundness (`LogosCheckerSound`), taken as
a hypothesis so that this build does not need Logos's proofs.
`Telos.rewrite_correct` (`TelosFull/Main.lean`) discharges it with Logos's
`proven_from_empty_valid`.
-/

namespace Telos

/-- **Correctness of the rewriter**, given Logos's checker soundness. Rewriting
a well-typed node gives an equivalent node. -/
theorem rewrite_correct_of_logos (hL : LogosCheckerSound) (t : Node) (h : t.WellTyped) :
    t.Equiv (rewrite t) :=
  rewriteWith_sound hL theoryRewriter defaultFuel t h

end Telos
