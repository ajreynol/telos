import Telos
import Cpc.SmtTranslate

/-!
# Children of well-typed applications are well typed

For the built-in operators telos rewrites under (Booleans, equality, arithmetic,
the non-indexed bit-vector operators),
an application whose translation has an SMT type has arguments whose
translations have SMT types. So the congruence steps of the driver need no
run-time check that the children are well typed (`Op.childrenTypedOfParent`):
`Certified.equiv` derives it from the parent (`children_wellTyped`).
-/

open Eo Smtm SmtEval

namespace Telos.ChildTyping

/-- `t`'s translation has an SMT type. -/
def Typed (t : Term) : Prop := __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Close `rule T = None` where an argument type `T` is `None`. -/
macro "close_none" : tactic => `(tactic| first | rfl | (simp [native_ite, native_Teq, __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_ite, __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret, __smtx_typeof_concat]) | (split <;> simp_all [native_ite, native_Teq, __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_ite, __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret, __smtx_typeof_concat]))

theorem typed_not (x : Term) (h : Typed (.Apply (.UOp .not) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .not) x) = SmtTerm.not (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_uneg (x : Term) (h : Typed (.Apply (.UOp .__eoo_neg_2) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .__eoo_neg_2) x) = SmtTerm.uneg (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_abs (x : Term) (h : Typed (.Apply (.UOp .abs) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .abs) x) = SmtTerm.abs (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_to_real (x : Term) (h : Typed (.Apply (.UOp .to_real) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .to_real) x) = SmtTerm.to_real (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_to_int (x : Term) (h : Typed (.Apply (.UOp .to_int) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .to_int) x) = SmtTerm.to_int (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_is_int (x : Term) (h : Typed (.Apply (.UOp .is_int) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .is_int) x) = SmtTerm.is_int (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_eq (x y : Term) (h : Typed (.Apply (.Apply (.UOp .eq) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .eq) x) y) = SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_and (x y : Term) (h : Typed (.Apply (.Apply (.UOp .and) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .and) x) y) = SmtTerm.and (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_or (x y : Term) (h : Typed (.Apply (.Apply (.UOp .or) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .or) x) y) = SmtTerm.or (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_imp (x y : Term) (h : Typed (.Apply (.Apply (.UOp .imp) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .imp) x) y) = SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_xor (x y : Term) (h : Typed (.Apply (.Apply (.UOp .xor) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .xor) x) y) = SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_plus (x y : Term) (h : Typed (.Apply (.Apply (.UOp .plus) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .plus) x) y) = SmtTerm.plus (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_mult (x y : Term) (h : Typed (.Apply (.Apply (.UOp .mult) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .mult) x) y) = SmtTerm.mult (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_neg (x y : Term) (h : Typed (.Apply (.Apply (.UOp .neg) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .neg) x) y) = SmtTerm.neg (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_qdiv (x y : Term) (h : Typed (.Apply (.Apply (.UOp .qdiv) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .qdiv) x) y) = SmtTerm.qdiv (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_div (x y : Term) (h : Typed (.Apply (.Apply (.UOp .div) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .div) x) y) = SmtTerm.div (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_mod (x y : Term) (h : Typed (.Apply (.Apply (.UOp .mod) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .mod) x) y) = SmtTerm.mod (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_qdiv_total (x y : Term) (h : Typed (.Apply (.Apply (.UOp .qdiv_total) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .qdiv_total) x) y) = SmtTerm.qdiv_total (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_div_total (x y : Term) (h : Typed (.Apply (.Apply (.UOp .div_total) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .div_total) x) y) = SmtTerm.div_total (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_mod_total (x y : Term) (h : Typed (.Apply (.Apply (.UOp .mod_total) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .mod_total) x) y) = SmtTerm.mod_total (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_lt (x y : Term) (h : Typed (.Apply (.Apply (.UOp .lt) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .lt) x) y) = SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_leq (x y : Term) (h : Typed (.Apply (.Apply (.UOp .leq) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .leq) x) y) = SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_gt (x y : Term) (h : Typed (.Apply (.Apply (.UOp .gt) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .gt) x) y) = SmtTerm.gt (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_geq (x y : Term) (h : Typed (.Apply (.Apply (.UOp .geq) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .geq) x) y) = SmtTerm.geq (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_ite (x y z : Term) (h : Typed (.Apply (.Apply (.Apply (.UOp .ite) x) y) z)) :
    Typed x ∧ Typed y ∧ Typed z := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.Apply (.UOp .ite) x) y) z) =
    SmtTerm.ite (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from rfl, __smtx_typeof.eq_def] at h <;> simp only at h
  refine ⟨?_, ?_, ?_⟩ <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> cases __smtx_typeof (__eo_to_smt z) <;> close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> cases __smtx_typeof (__eo_to_smt y) <;> close_none

/-! ## Bit-vector operators -/

theorem typed_bvnot (x : Term) (h : Typed (.Apply (.UOp .bvnot) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .bvnot) x) = SmtTerm.bvnot (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_bvneg (x : Term) (h : Typed (.Apply (.UOp .bvneg) x)) : Typed x := by
  unfold Typed at *; intro hx; apply h
  rw [show __eo_to_smt (.Apply (.UOp .bvneg) x) = SmtTerm.bvneg (__eo_to_smt x) from rfl,
    __smtx_typeof.eq_def] <;> simp only
  rw [hx]; close_none

theorem typed_bvnand (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvnand) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvnand) x) y) = SmtTerm.bvnand (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvnor (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvnor) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvnor) x) y) = SmtTerm.bvnor (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvxnor (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvxnor) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvxnor) x) y) = SmtTerm.bvxnor (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvcomp (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvcomp) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvcomp) x) y) = SmtTerm.bvcomp (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsub (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsub) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsub) x) y) = SmtTerm.bvsub (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvudiv (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvudiv) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvudiv) x) y) = SmtTerm.bvudiv (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvurem (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvurem) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvurem) x) y) = SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsdiv (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsdiv) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsdiv) x) y) = SmtTerm.bvsdiv (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsrem (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsrem) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsrem) x) y) = SmtTerm.bvsrem (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsmod (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsmod) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsmod) x) y) = SmtTerm.bvsmod (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvshl (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvshl) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvshl) x) y) = SmtTerm.bvshl (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvlshr (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvlshr) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvlshr) x) y) = SmtTerm.bvlshr (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvashr (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvashr) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvashr) x) y) = SmtTerm.bvashr (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvult (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvult) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvult) x) y) = SmtTerm.bvult (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvule (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvule) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvule) x) y) = SmtTerm.bvule (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvugt (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvugt) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvugt) x) y) = SmtTerm.bvugt (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvuge (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvuge) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvuge) x) y) = SmtTerm.bvuge (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvslt (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvslt) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvslt) x) y) = SmtTerm.bvslt (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsle (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsle) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsle) x) y) = SmtTerm.bvsle (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsgt (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsgt) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsgt) x) y) = SmtTerm.bvsgt (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvsge (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvsge) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvsge) x) y) = SmtTerm.bvsge (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvand (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvand) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvand) x) y) = SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvor (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvor) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvor) x) y) = SmtTerm.bvor (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvxor (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvxor) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvxor) x) y) = SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvadd (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvadd) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvadd) x) y) = SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_bvmul (x y : Term) (h : Typed (.Apply (.Apply (.UOp .bvmul) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .bvmul) x) y) = SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_concat (x y : Term) (h : Typed (.Apply (.Apply (.UOp .concat) x) y)) : Typed x ∧ Typed y := by
  unfold Typed at *
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .concat) x) y) = SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y) from rfl,
    __smtx_typeof.eq_def] at h <;> simp only at h
  constructor <;> intro hx <;> apply h <;> rw [hx]
  · close_none
  · cases __smtx_typeof (__eo_to_smt x) <;> close_none

theorem typed_stuck : ¬ Typed .Stuck := by
  unfold Typed; rw [show __eo_to_smt .Stuck = SmtTerm.None from rfl, __smtx_typeof.eq_def]; simp

theorem spine1 {head : Term} (hlem : ∀ x, Typed (.Apply head x) → Typed x) :
    ∀ xs : List Term, Typed ((AppShape.spine head (.exactly 1)).toEo xs) → ∀ x ∈ xs, Typed x
  | [x], h => by simp [AppShape.toEo, Arity.accepts] at h; simpa using hlem x h
  | [], h | _ :: _ :: _, h => by simp [AppShape.toEo, Arity.accepts] at h; exact absurd h typed_stuck

theorem spine2 {head : Term} (hlem : ∀ x y, Typed (.Apply (.Apply head x) y) → Typed x ∧ Typed y) :
    ∀ xs : List Term, Typed ((AppShape.spine head (.exactly 2)).toEo xs) → ∀ x ∈ xs, Typed x
  | [x, y], h => by
    simp [AppShape.toEo, Arity.accepts] at h
    have := hlem x y h; intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp_all
  | [], h | [_], h | _ :: _ :: _ :: _, h => by
    simp [AppShape.toEo, Arity.accepts] at h; exact absurd h typed_stuck

theorem spine3 {head : Term}
    (hlem : ∀ x y z, Typed (.Apply (.Apply (.Apply head x) y) z) → Typed x ∧ Typed y ∧ Typed z) :
    ∀ xs : List Term, Typed ((AppShape.spine head (.exactly 3)).toEo xs) → ∀ x ∈ xs, Typed x
  | [x, y, z], h => by
    simp [AppShape.toEo, Arity.accepts] at h
    have := hlem x y z h; intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> simp_all
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => by
    simp [AppShape.toEo, Arity.accepts] at h; exact absurd h typed_stuck

theorem chain {op : UserOp} (hlem : ∀ x y, Typed (.Apply (.Apply (.UOp op) x) y) → Typed x ∧ Typed y)
    (nil : Term) : ∀ xs : List Term, Typed (eoRightAssocNil op nil xs) → ∀ x ∈ xs, Typed x
  | [], _ => by simp
  | x :: xs, h => by
    have := hlem x _ h
    intro z hz; rcases List.mem_cons.1 hz with rfl | hz
    · exact this.1
    · exact chain hlem nil xs this.2 z hz

theorem rassoc {op : UserOp} {nil : Nil}
    (hlem : ∀ x y, Typed (.Apply (.Apply (.UOp op) x) y) → Typed x ∧ Typed y) :
    ∀ xs : List Term, Typed ((AppShape.rightAssocNil op nil).toEo xs) → ∀ x ∈ xs, Typed x := by
  intro xs h
  simp only [AppShape.toEo] at h
  split at h
  · exact chain hlem _ xs h
  · exact absurd h typed_stuck

/-- **Children of a well-typed application of a built-in operator are well typed.** -/
theorem children_wellTyped {op : Op} {cs : Array Node} (hc : op.childrenTypedOfParent = true)
    (h : (Node.app op cs).WellTyped) : ∀ c ∈ cs.toList, c.WellTyped := by
  have h' : Typed (op.eoShape.toEo (cs.toList.map Node.toEo)) := by
    rw [← Node.toEo_app]; exact h
  suffices hs : ∀ x ∈ cs.toList.map Node.toEo, Typed x by
    intro c hcm; exact hs _ (List.mem_map_of_mem hcm)
  cases op with
  | indexed k is => simp [Op.childrenTypedOfParent] at hc
  | node k f => simp [Op.childrenTypedOfParent] at hc
  | kind k =>
    cases k <;> simp only [Op.childrenTypedOfParent, Bool.false_eq_true] at hc <;>
      simp only [Op.eoShape, Kind.eoShape] at h'

    all_goals first
      | exact spine1 (fun x h => by first | exact typed_not x h | exact typed_uneg x h | exact typed_abs x h | exact typed_to_real x h | exact typed_to_int x h | exact typed_is_int x h | exact typed_bvnot x h | exact typed_bvneg x h) _ h'
      | exact spine2 (fun x y h => by first | exact typed_eq x y h | exact typed_imp x y h | exact typed_xor x y h | exact typed_neg x y h | exact typed_qdiv x y h | exact typed_div x y h | exact typed_mod x y h | exact typed_qdiv_total x y h | exact typed_div_total x y h | exact typed_mod_total x y h | exact typed_lt x y h | exact typed_leq x y h | exact typed_gt x y h | exact typed_geq x y h | exact typed_bvnand x y h | exact typed_bvnor x y h | exact typed_bvxnor x y h | exact typed_bvcomp x y h | exact typed_bvsub x y h | exact typed_bvudiv x y h | exact typed_bvurem x y h | exact typed_bvsdiv x y h | exact typed_bvsrem x y h | exact typed_bvsmod x y h | exact typed_bvshl x y h | exact typed_bvlshr x y h | exact typed_bvashr x y h | exact typed_bvult x y h | exact typed_bvule x y h | exact typed_bvugt x y h | exact typed_bvuge x y h | exact typed_bvslt x y h | exact typed_bvsle x y h | exact typed_bvsgt x y h | exact typed_bvsge x y h) _ h'
      | exact spine3 (fun x y z h => typed_ite x y z h) _ h'
      | exact rassoc (fun x y h => by first | exact typed_and x y h | exact typed_or x y h | exact typed_plus x y h | exact typed_mult x y h | exact typed_bvand x y h | exact typed_bvor x y h | exact typed_bvxor x y h | exact typed_bvadd x y h | exact typed_bvmul x y h | exact typed_concat x y h) _ h'

end Telos.ChildTyping
