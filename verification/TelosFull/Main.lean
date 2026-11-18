import TelosProofs.Axioms
import Cpc.Proofs.ProvenFromEmpty
import Cpc.Proofs.RuleSupport.Cong.Spine
import Cpc.Proofs.RuleSupport.SpineArgsSupport
import Cpc.Proofs.RuleSupport.SubstituteTypeSupport
import Cpc.Proofs.TypePreservation.Full
import Cpc.Proofs.RuleSupport.Cong.TrueSpine
import Cpc.Proofs.RuleSupport.Cong.TypeSpine
import Cpc.Proofs.Closed.Support

/-!
# The unconditional theorem

The default build (`TelosProofs`) proves `Telos.rewrite_correct_of_logos`, which
takes the Logos theorems it uses as the class `LogosFacts`
(`TelosProofs/Core/LogosFacts.lean`), so that it does not need Logos's proofs. This
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

theorem agrees_of {M N : SmtModel} (h : AgreesOnGlobals M N) : model_agrees_on_globals M N :=
  ⟨h.consts, h.funs, h.usortDom⟩

theorem agrees_to {M N : SmtModel} (h : model_agrees_on_globals M N) : AgreesOnGlobals M N :=
  ⟨h.consts, h.funs, h.usortDom⟩

/-- A true spine over `xs` and `ys`, extending one between the heads. -/
theorem congTrueSpine_foldl (M : SmtModel) (hM : model_wf M) :
    ∀ {h₁ h₂ : Term} {xs ys : List Term},
      CongSupport.CongTrueSpine M h₁ h₂ →
      List.Forall₂ (fun x y => HasBoolType (mkEq x y) ∧
        ∀ N, model_wf N → AgreesOnGlobals M N → TrueIn N (mkEq x y)) xs ys →
      CongSupport.CongTrueSpine M (xs.foldl Term.Apply h₁) (ys.foldl Term.Apply h₂) := by
  intro h₁ h₂ xs ys hh h
  induction h generalizing h₁ h₂ with
  | nil => exact hh
  | cons hxy _ ih =>
    refine ih (CongSupport.CongTrueSpine.app hh ?_ ?_)
    · exact (eo_interprets_true_iff M _).2 ⟨hxy.1, hxy.2 M hM (agrees_to (model_agrees_on_globals_refl M))⟩
    · intro N hN hAgree
      exact (eo_interprets_true_iff N _).2 ⟨hxy.1, hxy.2 N hN (agrees_to hAgree)⟩

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
  eval_bool M t hM h := by
    have hP := type_preservation M hM t (by unfold term_has_non_none_type; rw [h]; simp)
    rw [h] at hP
    exact bool_value_canonical hP
  cong_spine_model M hM head xs ys hq hb h :=
    ((eo_interprets_true_iff M _).1 (CongSupport.congTrueSpine_eq_true M hM _ _ ⟨hq.1, hq.2⟩ hb
      (congTrueSpine_foldl M hM (CongSupport.CongTrueSpine.refl head) h))).2
  cong_type_spine head xs ys ht h :=
    CongSupport.congTypeSpine_eq_has_bool_type _ _ ht
      (CongSupport.congTypeSpine_foldl (fun _ _ hxy => hxy) (CongSupport.CongTypeSpine.refl head) h)
  closed_eval P hc M N h := smt_model_eval_eq_of_eo_closed P hc M N (agrees_of h)
  uf_args i T xs h x hx :=
    SpineArgsSupport.spine_args_have_smt_translation (Term.UConst i T) xs (.uconst i T _) h x hx

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  rewrite_correct_of_logos t h

/-- **Correctness of the preprocessor.** The conjunction of the preprocessed
assertions is equivalent to that of the input assertions (and `true`). -/
theorem preprocess_correct (as : List Node) (h : (Preprocess.inputNode as).WellTyped) :
    (Preprocess.inputNode as).Equiv (Preprocess.preprocessCert as).1 :=
  preprocess_correct_of_logos as h

end Telos

#assert_axioms Telos.rewrite_correct
#assert_axioms Telos.preprocess_correct
