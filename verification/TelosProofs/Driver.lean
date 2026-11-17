import TelosProofs.Certified

/-!
# Correctness of the rewriting driver

The driver (`rewriteWith`) returns a certified rewrite (`Rw`): it chains the
certificates of the theory rewriters' responses, and certifies rewriting under
operators by congruence (`Certified.congr`, `Certified.congrBody`). So its
correctness is an instance of `Certified.equiv`, whatever the theory rewriters
and the fuel.
-/

namespace Telos

section
variable (hL : LogosCheckerSound)
include hL

/-- **Correctness of the driver**, for any theory rewriters. -/
theorem rewriteWith_sound (R : TheoryId → TheoryRewriter) (fuel : Nat) (n : Node)
    (h : n.WellTyped) : n.Equiv (rewriteWith R fuel n).1 :=
  (rewriteWith R fuel n).2.equiv hL h

/-- Every theory rewriter returns equivalent nodes: its responses are certified. -/
theorem TheoryRewriter.correct (R : TheoryRewriter) (n : Node) (h : n.WellTyped) :
    n.Equiv (R.preRewrite n).node ∧ n.Equiv (R.postRewrite n).node :=
  ⟨(R.preRewrite n).cert.equiv hL h, (R.postRewrite n).cert.equiv hL h⟩

end

end Telos
