import TelosProofs.Spec
import Cpc.Proofs.Common

/-!
# The algebra of `Node.Equiv`

`Node.Equiv` is stated through `eo_satisfiability`, which is what makes it the
meaning of a CPC step. To reason about it, this file shows it is the same as a
semantic relation on SMT terms:

`t.Equiv s ↔ t.WellTyped ∧ SmtEquiv t.toSmt s.toSmt`

where `SmtEquiv a b` says that `a` and `b` have the same SMT type and related
values (`smt_value_rel`: equal, or extensionally equal regular languages) in every
well-formed model. `SmtEquiv` is an equivalence relation and asks for no typing,
which makes it the convenient relation for congruence proofs.
-/

open Eo
open Smtm
open SmtEval
open RuleProofs

namespace Telos

/-- Same SMT type, and related values in every well-formed model. -/
def SmtEquiv (a b : SmtTerm) : Prop :=
  __smtx_typeof a = __smtx_typeof b ∧
  ∀ M, model_wf M → smt_value_rel (__smtx_model_eval M a) (__smtx_model_eval M b)

namespace SmtEquiv

theorem refl (a : SmtTerm) : SmtEquiv a a :=
  ⟨rfl, fun _ _ => smt_value_rel_refl _⟩

theorem symm {a b : SmtTerm} (h : SmtEquiv a b) : SmtEquiv b a :=
  ⟨h.1.symm, fun M hM => smt_value_rel_symm _ _ (h.2 M hM)⟩

theorem trans {a b c : SmtTerm} (h₁ : SmtEquiv a b) (h₂ : SmtEquiv b c) : SmtEquiv a c :=
  ⟨h₁.1.trans h₂.1, fun M hM => smt_value_rel_trans _ _ _ (h₁.2 M hM) (h₂.2 M hM)⟩

end SmtEquiv

/-! ## From `eo_satisfiability` to `SmtEquiv` -/

theorem typeof_eq_arm (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.eq a b) = __smtx_typeof_eq (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

theorem eval_not_arm (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not a) = __smtx_model_eval_not (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def]

theorem eval_eq_arm (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

theorem typeof_eq_eq_bool_iff (T U : SmtType) :
    __smtx_typeof_eq T U = SmtType.Bool ↔ T ≠ SmtType.None ∧ T = U := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None <;> by_cases hTU : T = U <;>
    simp [native_ite, native_Teq, hT, hTU]

/-- `=` always evaluates to a Boolean. -/
theorem eval_eq_boolean (v w : SmtValue) : ∃ b, __smtx_model_eval_eq v w = SmtValue.Boolean b := by
  unfold __smtx_model_eval_eq
  split <;> exact ⟨_, rfl⟩

theorem eval_not_eq_false_iff (v w : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_eq v w) = SmtValue.Boolean false ↔
      smt_value_rel v w := by
  rw [smt_value_rel_iff_model_eval_eq_true]
  obtain ⟨b, hb⟩ := eval_eq_boolean v w
  rw [hb]
  cases b <;> simp [__smtx_model_eval_not, native_not]

theorem smt_satisfiability_false_iff (t : SmtTerm) :
    smt_satisfiability t false ↔
      ∀ M, model_wf M → __smtx_model_eval M t = SmtValue.Boolean false := by
  constructor
  · intro h
    cases h with
    | intro_false h => exact h
  · exact smt_satisfiability.intro_false t

/-- **`Node.Equiv` is semantic equivalence of well-typed nodes.** -/
theorem Node.equiv_iff (t s : Node) :
    t.Equiv s ↔ t.WellTyped ∧ SmtEquiv t.toSmt s.toSmt := by
  have hTy : __smtx_typeof (__eo_to_smt (eqFormula t s)) =
      __smtx_typeof_eq t.smtType s.smtType := typeof_eq_arm _ _
  have hSat : eo_satisfiability (eoApp1 UserOp.not (eqFormula t s)) false ↔
      ∀ M, model_wf M → smt_value_rel (__smtx_model_eval M t.toSmt)
        (__smtx_model_eval M s.toSmt) := by
    change smt_satisfiability (SmtTerm.not (SmtTerm.eq t.toSmt s.toSmt)) false ↔ _
    rw [smt_satisfiability_false_iff]
    refine forall_congr' fun M => imp_congr_right fun _ => ?_
    rw [eval_not_arm, eval_eq_arm, eval_not_eq_false_iff]
  unfold Node.Equiv
  rw [hTy, typeof_eq_eq_bool_iff, hSat]
  exact ⟨fun ⟨⟨hw, he⟩, hv⟩ => ⟨hw, he, hv⟩, fun ⟨hw, he, hv⟩ => ⟨⟨hw, he⟩, hv⟩⟩

/-! ## Equivalence-relation laws -/

namespace Node.Equiv

theorem wellTyped_left {t s : Node} (h : t.Equiv s) : t.WellTyped :=
  ((Node.equiv_iff t s).1 h).1

theorem wellTyped_right {t s : Node} (h : t.Equiv s) : s.WellTyped := by
  obtain ⟨hw, he, _⟩ := (Node.equiv_iff t s).1 h
  intro hs
  exact hw (he.trans hs)

/-- Equivalent nodes have the same type. -/
theorem smtType_eq {t s : Node} (h : t.Equiv s) : t.smtType = s.smtType :=
  ((Node.equiv_iff t s).1 h).2.1

theorem refl (t : Node) (h : t.WellTyped) : t.Equiv t :=
  (Node.equiv_iff t t).2 ⟨h, SmtEquiv.refl _⟩

theorem symm {t s : Node} (h : t.Equiv s) : s.Equiv t :=
  (Node.equiv_iff s t).2 ⟨h.wellTyped_right, ((Node.equiv_iff t s).1 h).2.symm⟩

theorem trans {t s u : Node} (h₁ : t.Equiv s) (h₂ : s.Equiv u) : t.Equiv u :=
  (Node.equiv_iff t u).2
    ⟨h₁.wellTyped_left, ((Node.equiv_iff t s).1 h₁).2.trans ((Node.equiv_iff s u).1 h₂).2⟩

end Node.Equiv

end Telos
