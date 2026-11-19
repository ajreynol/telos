import TelosProofs.Core.LogosFacts
import Cpc.Proofs.TypePreservation.Full
import Cpc.Proofs.Closed.IsClosedRec
import Cpc.Proofs.RuleSupport.Cong.Core
import Cpc.Proofs.RuleSupport.Cong.HoCong

/-!
# Arguments of well-typed applications

The fields of `LogosFacts` about the arguments of well-typed applications
(`TelosProofs/Core/LogosFacts.lean`), from the Logos theorems they restate. They
are separate from `Main.lean` because they need only Logos's type preservation
and closedness developments, not its checker soundness.
-/

open Eo Smtm SmtEval CongSupport

namespace Telos.ChildArgs

theorem noNoneParts_of : ∀ T, type_has_no_none_components T → NoNoneParts T
  | SmtType.None, h => h
  | SmtType.TypeRef _, h => h
  | SmtType.Seq A, h => noNoneParts_of A h
  | SmtType.Set A, h => noNoneParts_of A h
  | SmtType.Map A B, h => ⟨noNoneParts_of A h.1, noNoneParts_of B h.2⟩
  | SmtType.FunType A B, h => ⟨noNoneParts_of A h.1, noNoneParts_of B h.2⟩
  | SmtType.DtcAppType A B, h => ⟨noNoneParts_of A h.1, noNoneParts_of B h.2⟩
  | SmtType.Bool, _ | SmtType.Int, _ | SmtType.Real, _ | SmtType.RegLan, _ | SmtType.BitVec _, _
  | SmtType.Char, _ | SmtType.USort _, _ | SmtType.Datatype _ _, _ => trivial

theorem type_no_none (t : SmtTerm) (h : __smtx_typeof t ≠ SmtType.None) :
    NoNoneParts (__smtx_typeof t) :=
  noNoneParts_of _ (term_type_has_no_none_components_of_non_none t h)

theorem tuple_args (x y : Term) (h : HasSmtType (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)) :
    HasSmtType x ∧ HasSmtType y :=
  tuple_args_have_smt_translation_of_has_smt_translation h

theorem uop1_arg (op : UserOp1) (idx x : Term) (h : HasSmtType (Term.Apply (Term.UOp1 op idx) x)) :
    HasSmtType x :=
  apply_uop1_arg_has_smt_translation_of_has_smt_translation h

theorem tuple_update_args (idx x y : Term)
    (h : HasSmtType (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)) :
    HasSmtType x ∧ HasSmtType y :=
  (tuple_update_index_nat_valid_and_args_have_smt_translation h).2

theorem update_args (idx x y : Term)
    (h : HasSmtType (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)) :
    HasSmtType x ∧ HasSmtType y :=
  (update_index_sel_and_args_have_smt_translation h).2

theorem dt_sel_arg (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (x : Term)
    (h : HasSmtType (Term.Apply (Term.DtSel s d i j) x)) : HasSmtType x :=
  apply_dt_sel_arg_has_smt_translation_of_has_smt_translation h

theorem smt_apply_args {F a : SmtTerm} (hS : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j)
    (hT : ∀ s d i, F ≠ SmtTerm.DtTester s d i) (h : __smtx_typeof (SmtTerm.Apply F a) ≠ SmtType.None) :
    __smtx_typeof F ≠ SmtType.None ∧ __smtx_typeof a ≠ SmtType.None := by
  have e := generic_apply_type_of_non_special_head_closed F a hS hT
  unfold generic_apply_type at e
  rw [e] at h
  constructor
  · intro hF; apply h; rw [hF]; simp [__smtx_typeof_apply]
  · intro ha; apply h; rw [ha]
    cases __smtx_typeof F <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq] <;>
      intros <;> simp_all

theorem dtcons_head_ne (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
    (∀ s' d' i' j', __eo_to_smt (Term.DtCons s d i) ≠ SmtTerm.DtSel s' d' i' j') ∧
    (∀ s' d' i', __eo_to_smt (Term.DtCons s d i) ≠ SmtTerm.DtTester s' d' i') := by
  constructor <;> intros <;> simp only [__eo_to_smt, native_ite] <;> split <;> simp

theorem appSpineRev_foldl : ∀ (xs : List Term) (t : Term),
    appSpineRev (xs.foldl Term.Apply t) = ((appSpineRev t).1, xs.reverse ++ (appSpineRev t).2)
  | [], t => by simp
  | x :: xs, t => by
    rw [List.foldl_cons, appSpineRev_foldl xs]
    simp [appSpineRev]

theorem mk_args {F : SmtTerm} (hS : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j)
    (hT : ∀ s d i, F ≠ SmtTerm.DtTester s d i) :
    ∀ ys : List SmtTerm, __smtx_typeof (mkSmtAppSpineRev F ys) ≠ SmtType.None →
      ∀ y ∈ ys, __smtx_typeof y ≠ SmtType.None
  | [], _ => by simp
  | y :: ys, h => by
    have := smt_apply_args (mkSmtAppSpineRev_ne_dt_sel hS ys) (mkSmtAppSpineRev_ne_dt_tester hT ys) h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact this.2
    · exact mk_args hS hT ys this.1 z hz

theorem dt_cons_args (s : native_String) (d : DatatypeDecl) (i : native_Nat) (xs : List Term)
    (h : HasSmtType (xs.foldl Term.Apply (Term.DtCons s d i))) : ∀ x ∈ xs, HasSmtType x := by
  have hsp := appSpineRev_foldl xs (Term.DtCons s d i)
  simp only [appSpineRev, List.append_nil] at hsp
  have e := eo_to_smt_appSpineRev_dtcons s d i _ (by rw [hsp])
  rw [hsp] at e
  unfold HasSmtType at h
  rw [e] at h
  have := mk_args (dtcons_head_ne s d i).1 (dtcons_head_ne s d i).2 _ h
  intro x hx
  exact this _ (List.mem_map_of_mem (List.mem_reverse.2 hx))

end Telos.ChildArgs
