import TelosProofs.Axioms
import Cpc.Proofs.ProvenFromEmpty
import Cpc.Proofs.RuleSupport.Cong.Spine
import Cpc.Proofs.RuleSupport.SpineArgsSupport
import Cpc.Proofs.RuleSupport.SubstituteTypeSupport
import Cpc.Proofs.TypePreservation.Full

/-!
# The unconditional theorem

The default build (`TelosProofs`) proves `Telos.rewrite_correct_of_logos`, which
takes the Logos theorems it uses as the class `LogosFacts`
(`TelosProofs/LogosFacts.lean`), so that it does not need Logos's proofs. This
library, built with `lake build TelosFull`, imports them and proves the instance,
each field from the Logos theorem it restates. So the restatements stay in sync
with the pinned Logos. Then it derives the unconditional `Telos.rewrite_correct`
and audits its axioms.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- Logos's `eo_interprets M t true`, unfolded. -/
theorem eo_interprets_true_iff (M : SmtModel) (t : Term) :
    eo_interprets M t true ↔ HasBoolType t ∧ TrueIn M t := by
  constructor
  · intro h
    cases h with
    | intro_true _ _ hTy hEval => exact ⟨hTy, hEval⟩
  · intro ⟨hTy, hEval⟩
    exact smt_interprets.intro_true M _ hTy hEval

/-- `Valid` is Logos's notion of a valid formula. -/
theorem valid_iff (t : Term) :
    Valid t ↔ RuleProofs.eo_has_bool_type t ∧ ∀ M, model_wf M → eo_interprets M t true := by
  constructor
  · intro ⟨hTy, hTrue⟩
    exact ⟨hTy, fun M hM => (eo_interprets_true_iff M t).2 ⟨hTy, hTrue M hM⟩⟩
  · intro ⟨hTy, hInt⟩
    exact ⟨hTy, fun M hM => ((eo_interprets_true_iff M t).1 (hInt M hM)).2⟩

instance logosFacts : LogosFacts where
  checker_sound cs P hT hC hP := (valid_iff P).2 (proven_from_empty_valid cs P hT hC hP)
  cong_spine head xs ys ht h :=
    (valid_iff _).2 (CongSupport.cong_spine_valid head xs ys ht (h.imp fun h => (valid_iff _).1 h))
  eq_valid_iff a b := (valid_iff _).trans (RuleProofs.eq_valid_iff a b)
  value_rel_refl := RuleProofs.smt_value_rel_refl
  value_rel_symm := RuleProofs.smt_value_rel_symm
  value_rel_trans := RuleProofs.smt_value_rel_trans
  and_or_rest op x r hop h := by
    have hHead : SpineArgsSupport.SpineArgsHead (Term.UOp op) [x, r].length := by
      rcases hop with rfl | rfl
      exacts [.and, .or]
    exact SpineArgsSupport.spine_args_have_smt_translation _ [x, r] hHead h r (by simp)
  seq_type_wf x _ hNN hTy := smt_term_seq_type_wf_of_non_none x hNN hTy
  eo_typeof_bool t h := by
    apply SubstituteSupport.eo_typeof_eq_of_smt_type_eq _ _
    · show __smtx_typeof (__eo_to_smt t) ≠ SmtType.None
      rw [h]; simp
    · simp [__eo_to_smt_type, __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        SmtEval.native_and]
    · rw [h]; rfl

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  rewrite_correct_of_logos t h

end Telos

#assert_axioms Telos.rewrite_correct
