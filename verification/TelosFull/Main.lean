import TelosProofs.Axioms
import Cpc.Proofs.ProvenFromEmpty

/-!
# The unconditional theorem

The default build (`TelosProofs`) proves `Telos.rewrite_correct_of_logos`, which
takes Logos's checker soundness as the hypothesis `LogosCheckerSound`, so that it
does not need Logos's proofs. This library, built with `lake build TelosFull`,
imports them. It proves `LogosCheckerSound` from Logos's `proven_from_empty_valid`:
that the restatement in `TelosProofs/LogosSound.lean` matches Logos, and so
stays in sync with the pinned commit. Then it derives the unconditional
`Telos.rewrite_correct`, and audits its axioms.
-/

namespace Telos

/-- `LogosCheckerSound` is Logos's theorem. -/
theorem logosCheckerSound : LogosCheckerSound := proven_from_empty_valid

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  rewrite_correct_of_logos logosCheckerSound t h

end Telos

#assert_axioms Telos.rewrite_correct
