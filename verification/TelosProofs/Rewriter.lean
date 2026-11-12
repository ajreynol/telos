import TelosProofs.Spec
import Cpc.Proofs.Common

/-!
# Correctness of the rewriter

The central theorem: rewriting a well-typed node yields an equivalent node.
`rewrite` is still the identity, so the proof is reflexivity of `Node.Equiv`. The
statement is final and stays fixed as the rewriter grows.
-/

open Eo
open Smtm

namespace Telos

private theorem typeof_eq_arm (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.eq a b) = __smtx_typeof_eq (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

private theorem eval_not_arm (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not a) = __smtx_model_eval_not (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def]

private theorem eval_eq_arm (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

/-- Every well-typed node is equivalent to itself. -/
theorem Node.Equiv.refl (t : Node) (h : t.WellTyped) : t.Equiv t := by
  have hTy : __smtx_typeof (__eo_to_smt t.toEo) ≠ SmtType.None := h
  refine ⟨?_, ?_⟩
  · change __smtx_typeof (SmtTerm.eq (__eo_to_smt t.toEo) (__eo_to_smt t.toEo)) = SmtType.Bool
    rw [typeof_eq_arm]
    exact RuleProofs.smtx_typeof_eq_refl _ hTy
  · refine smt_satisfiability.intro_false _ fun M _ => ?_
    change __smtx_model_eval M
        (SmtTerm.not (SmtTerm.eq (__eo_to_smt t.toEo) (__eo_to_smt t.toEo))) = _
    rw [eval_not_arm, eval_eq_arm, RuleProofs.smtx_model_eval_eq_refl]
    simp [__smtx_model_eval_not, SmtEval.native_not]

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  Node.Equiv.refl t h

end Telos
