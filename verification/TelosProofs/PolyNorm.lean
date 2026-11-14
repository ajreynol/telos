import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Cpc.Logos
import TelosProofs.TermOrder

/-!
# Logos's arithmetic normal form is canonical

`arith_poly_norm` accepts `(= a b)` when `__get_arith_poly_norm a` and
`__get_arith_poly_norm b` are the same term. To show statically that it accepts
an equation, it is enough to show that the two normal forms have the same
*value*, read as a polynomial over the atoms (`get_norm_eq_of_polyVal_eq`):

* `polyVal` reads a polynomial term (`@@poly`, `@@mon`, `eo` lists of variables)
  as an element of `MvPolynomial Term ℚ`. Logos's operations `__poly_add`,
  `__poly_neg`, `__poly_mul_mon`, `__poly_mul`, `__mon_mul_mon` and
  `__mvar_mul_mvar` are addition, negation and multiplication on values
  (`polyVal_add`, …). These need no property of the term order.
* `WfPoly`: monomials in strictly decreasing order (`native_tcmp`), each a list
  of variables in decreasing order, with nonzero rational coefficients.
  `__get_arith_poly_norm` only produces well-formed polynomials (`get_norm_wf`).
* Well-formed polynomials with the same value are equal
  (`WfPoly.eq_of_polyVal_eq`). This is where the order laws of
  `TelosProofs.TermOrder` are used.

So any normalizer whose output has the same polynomial value as its input, by
whatever algorithm, produces equations `arith_poly_norm` accepts.
-/
set_option linter.internalConstructors false

open Eo SmtEval MvPolynomial

namespace Telos.PolyNorm

abbrev P := MvPolynomial Term ℚ

/-! ## Values of Logos's polynomial terms -/

/-- The coefficient a monomial carries. Only rationals occur in normal forms; the
other cases are chosen so that the homomorphism lemmas hold on any input. -/
def coeffOf : Term → ℚ
  | .Rational q => q
  | _ => 0

/-- The product of the variables of a monomial (an `eo` list). -/
noncomputable def varsVal : Term → P
  | .Apply (.Apply .__eo_List_cons a) l => X a * varsVal l
  | _ => 1

noncomputable def monVal : Term → P
  | .Apply (.Apply (.UOp UserOp._at__at_mon) vs) c => C (coeffOf c) * varsVal vs
  | _ => 0

noncomputable def polyVal : Term → P
  | .Apply (.Apply (.UOp UserOp._at__at_poly) m) p => monVal m + polyVal p
  | _ => 0

@[simp] theorem polyVal_cons (m p : Term) :
    polyVal (.Apply (.Apply (.UOp UserOp._at__at_poly) m) p) = monVal m + polyVal p := rfl
@[simp] theorem polyVal_zero : polyVal (.UOp UserOp._at__at_poly_zero) = 0 := rfl
@[simp] theorem monVal_mon (vs c : Term) :
    monVal (.Apply (.Apply (.UOp UserOp._at__at_mon) vs) c) = C (coeffOf c) * varsVal vs := rfl
@[simp] theorem varsVal_cons (a l : Term) :
    varsVal (.Apply (.Apply .__eo_List_cons a) l) = X a * varsVal l := rfl
@[simp] theorem varsVal_nil : varsVal .__eo_List_nil = 1 := rfl

/-! ## Helpers about Eunoia's primitive operations -/

theorem mk_apply_of_ne {f x : Term} (h : __eo_mk_apply f x ≠ .Stuck) :
    f ≠ .Stuck ∧ x ≠ .Stuck ∧ __eo_mk_apply f x = .Apply f x := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

theorem ite_cases {c x y : Term} (h : __eo_ite c x y ≠ .Stuck) :
    (c = .Boolean true ∧ __eo_ite c x y = x) ∨ (c = .Boolean false ∧ __eo_ite c x y = y) := by
  simp only [__eo_ite, native_ite, native_teq] at h ⊢
  by_cases h1 : c = .Boolean true
  · simp [h1]
  · by_cases h2 : c = .Boolean false
    · simp [h2]
    · simp [h1, h2] at h

theorem coeffOf_add {c₁ c₂ : Term} (h : __eo_add c₁ c₂ ≠ .Stuck) :
    coeffOf (__eo_add c₁ c₂) = coeffOf c₁ + coeffOf c₂ := by
  cases c₁ <;> cases c₂ <;> simp_all [__eo_add, coeffOf, native_qplus, __eo_requires, native_ite,
    native_teq]

theorem coeffOf_mul {c₁ c₂ : Term} (h : __eo_mul c₁ c₂ ≠ .Stuck) :
    coeffOf (__eo_mul c₁ c₂) = coeffOf c₁ * coeffOf c₂ := by
  cases c₁ <;> cases c₂ <;> simp_all [__eo_mul, coeffOf, native_qmult, __eo_requires, native_ite,
    native_teq]

theorem coeffOf_neg {c : Term} (h : __eo_neg c ≠ .Stuck) : coeffOf (__eo_neg c) = - coeffOf c := by
  cases c <;> simp_all [__eo_neg, coeffOf, native_qneg]

/-! ## The polynomial operations are ring operations on values -/

theorem polyVal_neg : ∀ p : Term, __poly_neg p ≠ .Stuck → polyVal (__poly_neg p) = - polyVal p := by
  intro p h
  fun_induction __poly_neg p with
  | case1 => simp [polyVal]
  | case2 a c p ih =>
    obtain ⟨h1, h2, e1⟩ := mk_apply_of_ne h
    obtain ⟨-, h3, e2⟩ := mk_apply_of_ne h1
    obtain ⟨-, h4, e3⟩ := mk_apply_of_ne h3
    rw [e1, e2, e3, polyVal, ih h2, polyVal, monVal, monVal, coeffOf_neg h4]
    simp only [map_neg]; ring
  | case3 p hp => exact absurd rfl h

theorem eo_eq_of_ne {a b : Term} (ha : a ≠ .Stuck) (hb : b ≠ .Stuck) :
    __eo_eq a b = .Boolean (decide (b = a)) := by
  cases a <;> cases b <;> simp_all [__eo_eq, native_teq]

theorem add_eq_zero_coeff {c₁ c₂ : Term} (h : __eo_add c₁ c₂ = .Rational (native_mk_rational 0 1)) :
    coeffOf c₁ + coeffOf c₂ = 0 := by
  have hne : __eo_add c₁ c₂ ≠ .Stuck := by rw [h]; simp
  rw [← coeffOf_add hne, h]; simp [coeffOf, native_mk_rational]

theorem polyVal_add : ∀ p q : Term, __poly_add p q ≠ .Stuck →
    polyVal (__poly_add p q) = polyVal p + polyVal q := by
  intro p q h
  fun_induction __poly_add p q with
  | case1 => exact absurd rfl h
  | case2 => exact absurd rfl h
  | case3 a1 c1 p1 a2 c2 p2 v0 v1 v2 v3 v4 ih1 ih2 ih3 =>
    rcases ite_cases h with ⟨hc, e⟩ | ⟨hc, e⟩ <;> rw [e] at h ⊢
    · -- Same monomial: add the coefficients.
      have ha1 : a1 ≠ .Stuck := by rintro rfl; simp [__eo_eq] at hc
      have ha2 : a2 ≠ .Stuck := by rintro rfl; cases a1 <;> simp [__eo_eq] at hc
      rw [eo_eq_of_ne ha1 ha2] at hc
      have ha : a2 = a1 := by simpa using hc
      subst ha
      rcases ite_cases h with ⟨hz, e2⟩ | ⟨hz, e2⟩ <;> rw [e2] at h ⊢
      · have hv4 : v4 ≠ .Stuck := by rintro hv; simp [hv, __eo_eq] at hz
        rw [eo_eq_of_ne hv4 (by simp)] at hz
        have hz' : v4 = .Rational (native_mk_rational 0 1) := by simpa [eq_comm] using hz
        have hsum := add_eq_zero_coeff hz'
        rw [ih1 h]
        simp only [polyVal, monVal]
        have hz0 : C (coeffOf c1) * varsVal a2 + C (coeffOf c2) * varsVal a2 = (0 : P) := by
          rw [← add_mul, ← map_add, hsum]; simp
        linear_combination -hz0
      · obtain ⟨h1, h2, e3⟩ := mk_apply_of_ne h
        obtain ⟨-, h3, e4⟩ := mk_apply_of_ne h1
        obtain ⟨-, h4, e5⟩ := mk_apply_of_ne h3
        rw [e3, e4, e5, polyVal, ih1 h2]
        simp only [v0, polyVal, monVal]
        rw [show coeffOf v4 = coeffOf c1 + coeffOf c2 from coeffOf_add h4, map_add]
        ring
    · rcases ite_cases h with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2] at h ⊢
      · obtain ⟨-, h2, e3⟩ := mk_apply_of_ne h
        rw [e3, polyVal, ih2 h2]
        simp only [v0, v1, v2, polyVal]
        ring
      · obtain ⟨-, h2, e3⟩ := mk_apply_of_ne h
        rw [e3, polyVal, ih3 h2]
        simp only [v0, v1, v2, polyVal]
        ring
  | case4 p => simp [polyVal]
  | case5 p _ => simp [polyVal]
  | case6 => exact absurd rfl h

theorem varsVal_mul : ∀ a b : Term, __mvar_mul_mvar a b ≠ .Stuck →
    varsVal (__mvar_mul_mvar a b) = varsVal a * varsVal b := by
  intro a b h
  fun_induction __mvar_mul_mvar a b with
  | case1 => exact absurd rfl h
  | case2 => exact absurd rfl h
  | case3 a1 a2 c1 c2 v0 v1 ih1 ih2 =>
    rcases ite_cases h with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] at h ⊢
    · obtain ⟨-, h2, e2⟩ := mk_apply_of_ne h
      rw [e2, varsVal, ih1 h2]; simp only [v0, v1, varsVal]; ring
    · obtain ⟨-, h2, e2⟩ := mk_apply_of_ne h
      rw [e2, varsVal, ih2 h2]; simp only [v0, v1, varsVal]; ring
  | case4 a2 _ => simp [varsVal]
  | case5 c2 _ _ => simp [varsVal]
  | case6 => exact absurd rfl h

theorem monVal_mul {m₁ m₂ : Term} (h : __mon_mul_mon m₁ m₂ ≠ .Stuck) :
    monVal (__mon_mul_mon m₁ m₂) = monVal m₁ * monVal m₂ := by
  unfold __mon_mul_mon at h ⊢
  split at h
  · obtain ⟨h1, h2, e1⟩ := mk_apply_of_ne h
    obtain ⟨-, h3, e2⟩ := mk_apply_of_ne h1
    rw [e1, e2, monVal, monVal, monVal, varsVal_mul _ _ h3, coeffOf_mul h2, map_mul]
    ring
  · exact absurd rfl h

theorem poly_add_args {p q : Term} (h : __poly_add p q ≠ .Stuck) : p ≠ .Stuck ∧ q ≠ .Stuck := by
  constructor <;> rintro rfl
  · simp [__poly_add] at h
  · cases p <;> simp [__poly_add] at h

theorem polyVal_mul_mon : ∀ m p : Term, __poly_mul_mon m p ≠ .Stuck →
    polyVal (__poly_mul_mon m p) = monVal m * polyVal p := by
  intro m p h
  fun_induction __poly_mul_mon m p with
  | case1 => exact absurd rfl h
  | case2 m1 m2 p2 hm ih =>
    obtain ⟨h1, h2⟩ := poly_add_args h
    rw [polyVal_add _ _ h, ih h2]
    obtain ⟨h3, -, e1⟩ := mk_apply_of_ne h1
    obtain ⟨-, h4, e2⟩ := mk_apply_of_ne h3
    rw [e1, e2, polyVal_cons, polyVal_zero, monVal_mul h4, polyVal_cons]
    ring
  | case3 => simp [polyVal]
  | case4 => exact absurd rfl h

theorem polyVal_mul : ∀ p q : Term, __poly_mul p q ≠ .Stuck →
    polyVal (__poly_mul p q) = polyVal p * polyVal q := by
  intro p q h
  fun_induction __poly_mul p q with
  | case1 => exact absurd rfl h
  | case2 => exact absurd rfl h
  | case3 m p1 p _ ih =>
    obtain ⟨h1, h2⟩ := poly_add_args h
    rw [polyVal_add _ _ h, polyVal_mul_mon _ _ h1, ih h2, polyVal_cons]
    ring
  | case4 => simp [polyVal]
  | case5 => simp [polyVal]
  | case6 => exact absurd rfl h

end Telos.PolyNorm
namespace Telos.PolyNorm
open Telos.TermOrder

/-! ## Terms are linearly ordered by `termCmp` -/

theorem termCmp_gt_iff (a b : Term) : termCmp a b = .gt ↔ termCmp b a = .lt := by
  rw [termCmp_swap a b]; cases termCmp a b <;> simp [Ordering.swap]

theorem termCmp_lt_or_eq {a b : Term} (h : termCmp a b ≠ .gt) : termCmp a b = .lt ∨ a = b := by
  cases e : termCmp a b
  · exact Or.inl rfl
  · exact Or.inr ((termCmp_eq_iff a b).1 e)
  · exact absurd e h

instance termLinearOrder : LinearOrder Term where
  le a b := termCmp a b ≠ .gt
  lt a b := termCmp a b = .lt
  le_refl a := by simp [(termCmp_eq_iff a a).2 rfl]
  le_trans a b c h1 h2 := by
    rcases termCmp_lt_or_eq h1 with h1 | rfl
    · rcases termCmp_lt_or_eq h2 with h2 | rfl
      · rw [termCmp_trans a b c h1 h2]; simp
      · rw [h1]; simp
    · exact h2
  lt_iff_le_not_ge a b := by
    show termCmp a b = .lt ↔ termCmp a b ≠ .gt ∧ ¬ termCmp b a ≠ .gt
    simp only [ne_eq, termCmp_gt_iff b a]
    cases termCmp a b <;> simp
  le_antisymm a b h1 h2 := by
    rcases termCmp_lt_or_eq h1 with h1 | e
    · exact absurd ((termCmp_gt_iff b a).2 h1) h2
    · exact e
  le_total a b := by
    show termCmp a b ≠ .gt ∨ termCmp b a ≠ .gt
    simp only [ne_eq, termCmp_gt_iff b a]
    cases termCmp a b <;> simp
  toDecidableLE := fun a b => inferInstanceAs (Decidable (termCmp a b ≠ .gt))

theorem term_lt_iff (a b : Term) : a < b ↔ native_tcmp a b = true := by
  rw [native_tcmp_iff]; rfl

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder

/-! ## Canonicity of well-formed normal forms -/

/-- The variables of a monomial, as a list. -/
def toL : Term → List Term
  | .Apply (.Apply .__eo_List_cons a) l => a :: toL l
  | _ => []

/-- `v` is an `eo` list of variables. -/
def IsVars : Term → Prop
  | .Apply (.Apply .__eo_List_cons _) l => IsVars l
  | .__eo_List_nil => True
  | _ => False

/-- A well-formed monomial: a list of variables, largest first, with repeats. -/
def WfVars (v : Term) : Prop := IsVars v ∧ (toL v).Pairwise (· ≥ ·)

/-- The exponent vector of a monomial. -/
noncomputable def expOf (v : Term) : Term →₀ ℕ := Multiset.toFinsupp (toL v : Multiset Term)

theorem toL_cons (a l : Term) : toL (.Apply (.Apply .__eo_List_cons a) l) = a :: toL l := rfl

theorem expOf_cons (a l : Term) :
    expOf (.Apply (.Apply .__eo_List_cons a) l) = Finsupp.single a 1 + expOf l := by
  rw [expOf, expOf, toL_cons, ← Multiset.cons_coe, ← Multiset.singleton_add,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem varsVal_eq_monomial (v : Term) : varsVal v = monomial (expOf v) 1 := by
  fun_induction varsVal v with
  | case1 a l ih =>
    rw [ih, expOf_cons, X, monomial_mul_monomial, one_mul]
  | case2 v hv =>
    have : toL v = [] := by unfold toL; split <;> simp_all
    simp [expOf, this]

theorem eq_of_toL_eq : ∀ {v w : Term}, IsVars v → IsVars w → toL v = toL w → v = w := by
  intro v w hv hw h
  fun_induction toL v generalizing w with
  | case1 a l ih =>
    unfold IsVars at hv
    unfold IsVars at hw; split at hw
    · next b m =>
      simp only [toL_cons, List.cons.injEq] at h
      rw [h.1, ih hv hw h.2]
    · simp [toL] at h
    · exact hw.elim
  | case2 v hv' =>
    unfold IsVars at hv; split at hv
    · next a l => exact absurd rfl (hv' a l)
    · unfold IsVars at hw; split at hw
      · next b m => simp [toL] at h
      · rfl
      · exact hw.elim
    · exact hv.elim

theorem expOf_inj {v w : Term} (hv : WfVars v) (hw : WfVars w) (h : expOf v = expOf w) : v = w := by
  apply eq_of_toL_eq hv.1 hw.1
  have hm : (toL v : Multiset Term) = (toL w : Multiset Term) := Multiset.toFinsupp.injective h
  exact List.Perm.eq_of_pairwise' hv.2 hw.2 (Multiset.coe_eq_coe.1 hm)

/-- The entries `(variables, coefficient)` of a polynomial term. -/
def entries : Term → List (Term × Term)
  | .Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon) v) c)) p =>
    (v, c) :: entries p
  | _ => []

/-- `p` is a polynomial term: monomials ending in `@@poly_zero`. -/
def IsPoly : Term → Prop
  | .Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon) _) _)) p =>
    IsPoly p
  | .UOp UserOp._at__at_poly_zero => True
  | _ => False

/-- Well-formed entries: monomials in decreasing order, each well formed, with
nonzero rational coefficients. -/
def WfEntries (E : List (Term × Term)) : Prop :=
  (∀ e ∈ E, WfVars e.1 ∧ ∃ q : ℚ, e.2 = .Rational q ∧ q ≠ 0) ∧ E.Pairwise (fun e f => f.1 < e.1)

/-- A well-formed polynomial term: Logos's normal forms are these. -/
def WfPoly (p : Term) : Prop := IsPoly p ∧ WfEntries (entries p)

noncomputable def sumE (E : List (Term × Term)) : P :=
  (E.map fun e => monomial (expOf e.1) (coeffOf e.2)).sum

theorem sumE_cons (e : Term × Term) (E : List (Term × Term)) :
    sumE (e :: E) = monomial (expOf e.1) (coeffOf e.2) + sumE E := by
  simp [sumE]

theorem polyVal_eq_sumE (p : Term) (hp : IsPoly p) : polyVal p = sumE (entries p) := by
  fun_induction entries p with
  | case1 v c p ih =>
    rw [polyVal_cons, monVal_mon, sumE_cons, ← ih hp, varsVal_eq_monomial, C_mul_monomial, mul_one]
  | case2 p hp' =>
    unfold IsPoly at hp; split at hp
    · next v c q => exact absurd rfl (hp' v c q)
    · simp [sumE]
    · exact hp.elim

theorem coeff_sumE_of_not_mem {v : Term} (hv : WfVars v) :
    ∀ E : List (Term × Term), (∀ e ∈ E, WfVars e.1) → (∀ e ∈ E, e.1 ≠ v) →
      (sumE E).coeff (expOf v) = 0
  | [], _, _ => by simp [sumE]
  | e :: E, hw, hne => by
    rw [sumE_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial,
      coeff_sumE_of_not_mem hv E (fun f hf => hw f (by simp [hf])) (fun f hf => hne f (by simp [hf]))]
    have : expOf e.1 ≠ expOf v := fun h => hne e (by simp) (expOf_inj (hw e (by simp)) hv h)
    simp [this]

theorem WfEntries.tail {e : Term × Term} {E : List (Term × Term)} (h : WfEntries (e :: E)) :
    WfEntries E :=
  ⟨fun f hf => h.1 f (List.mem_cons_of_mem e hf), (List.pairwise_cons.1 h.2).2⟩

theorem WfEntries.head_vars {v c : Term} {E : List (Term × Term)} (h : WfEntries ((v, c) :: E)) :
    WfVars v := (h.1 (v, c) List.mem_cons_self).1

theorem WfEntries.head_coeff {v c : Term} {E : List (Term × Term)} (h : WfEntries ((v, c) :: E)) :
    coeffOf c ≠ 0 := by
  obtain ⟨q, hq, hq0⟩ := (h.1 (v, c) List.mem_cons_self).2
  subst hq; exact hq0

theorem WfEntries.vars {E : List (Term × Term)} (h : WfEntries E) : ∀ e ∈ E, WfVars e.1 :=
  fun e he => (h.1 e he).1

theorem coeff_sumE_head {v c : Term} {E : List (Term × Term)} (h : WfEntries ((v, c) :: E)) :
    (sumE ((v, c) :: E)).coeff (expOf v) = coeffOf c := by
  have hz : (sumE E).coeff (expOf v) = 0 := by
    apply coeff_sumE_of_not_mem h.head_vars E h.tail.vars
    intro f hf e
    have := List.rel_of_pairwise_cons h.2 hf
    rw [e] at this; exact lt_irrefl _ this
  rw [sumE_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial, ite_eq_left_iff.mpr (fun h => absurd rfl h), hz, add_zero]

/-- Every monomial of `(w, d) :: E` is below `v`, so `v`'s coefficient there is zero. -/
theorem coeff_sumE_of_lt {v : Term} (hv : WfVars v) {w d : Term} {E : List (Term × Term)}
    (h : WfEntries ((w, d) :: E)) (hlt : w < v) : (sumE ((w, d) :: E)).coeff (expOf v) = 0 := by
  apply coeff_sumE_of_not_mem hv _ h.vars
  intro f hf e
  rcases List.mem_cons.1 hf with rfl | hf
  · exact (ne_of_lt hlt) e
  · have := List.rel_of_pairwise_cons h.2 hf
    rw [e] at this; exact lt_asymm this hlt

theorem entries_eq : ∀ E F : List (Term × Term), WfEntries E → WfEntries F → sumE E = sumE F → E = F
  | [], [], _, _, _ => rfl
  | [], (w, d) :: F, _, hF, h => by
    have := coeff_sumE_head hF
    rw [← h] at this
    exact absurd (by simpa [sumE] using this.symm) hF.head_coeff
  | (v, c) :: E, [], hE, _, h => by
    have := coeff_sumE_head hE
    rw [h] at this
    exact absurd (by simpa [sumE] using this.symm) hE.head_coeff
  | (v, c) :: E, (w, d) :: F, hE, hF, h => by
    have hvw : v = w := by
      rcases lt_trichotomy v w with hlt | heq | hgt
      · have h1 := coeff_sumE_head hF
        rw [← h, coeff_sumE_of_lt hF.head_vars hE hlt] at h1
        exact absurd h1.symm hF.head_coeff
      · exact heq
      · have h1 := coeff_sumE_head hE
        rw [h, coeff_sumE_of_lt hE.head_vars hF hgt] at h1
        exact absurd h1.symm hE.head_coeff
    subst hvw
    have hcd : c = d := by
      have h1 := coeff_sumE_head hE
      rw [h, coeff_sumE_head hF] at h1
      obtain ⟨q, hq, -⟩ := (hE.1 (v, c) List.mem_cons_self).2
      obtain ⟨r, hr, -⟩ := (hF.1 (v, d) List.mem_cons_self).2
      subst hq hr; simp only [coeffOf] at h1; rw [h1]
    subst hcd
    rw [entries_eq E F hE.tail hF.tail (by rw [sumE_cons, sumE_cons] at h; exact add_left_cancel h)]

theorem eq_of_entries_eq : ∀ {p q : Term}, IsPoly p → IsPoly q → entries p = entries q → p = q := by
  intro p q hp hq h
  fun_induction entries p generalizing q with
  | case1 v c p ih =>
    unfold IsPoly at hp hq; split at hq
    · next w d q' =>
      simp only [entries, List.cons.injEq, Prod.mk.injEq] at h
      rw [h.1.1, h.1.2, ih hp hq h.2]
    · simp [entries] at h
    · exact hq.elim
  | case2 p hp' =>
    unfold IsPoly at hp; split at hp
    · next v c q' => exact absurd rfl (hp' v c q')
    · unfold IsPoly at hq; split at hq
      · simp [entries] at h
      · rfl
      · exact hq.elim
    · exact hp.elim

/-- **Canonicity**: well-formed polynomial terms with the same value are equal. -/
theorem WfPoly.eq_of_polyVal_eq {p q : Term} (hp : WfPoly p) (hq : WfPoly q)
    (h : polyVal p = polyVal q) : p = q := by
  rw [polyVal_eq_sumE p hp.1, polyVal_eq_sumE q hq.1] at h
  exact eq_of_entries_eq hp.1 hq.1 (entries_eq _ _ hp.2 hq.2 h)

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder

/-! ## Logos's operations produce well-formed polynomials -/

@[simp] theorem entries_cons (v c p : Term) :
    entries (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon) v) c)) p) =
      (v, c) :: entries p := rfl
@[simp] theorem entries_zero : entries (.UOp UserOp._at__at_poly_zero) = [] := rfl
@[simp] theorem isPoly_cons (v c p : Term) :
    IsPoly (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon) v) c)) p) ↔
      IsPoly p := Iff.rfl
@[simp] theorem isPoly_zero : IsPoly (.UOp UserOp._at__at_poly_zero) := trivial

theorem WfPoly.zero : WfPoly (.UOp UserOp._at__at_poly_zero) := ⟨trivial, by simp [WfEntries]⟩

theorem WfPoly.cons {v c p : Term} :
    WfPoly (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon) v) c)) p) ↔
      WfVars v ∧ (∃ q : ℚ, c = .Rational q ∧ q ≠ 0) ∧ WfPoly p ∧ ∀ e ∈ entries p, e.1 < v := by
  simp only [WfPoly, WfEntries, entries_cons, isPoly_cons, List.forall_mem_cons, List.pairwise_cons]
  tauto

theorem cmp_true {a b : Term} (h : __eo_cmp a b = .Boolean true) : a < b := by
  rw [term_lt_iff]
  cases a <;> cases b <;> simp_all [__eo_cmp]

theorem cmp_false {a b : Term} (h : __eo_cmp a b = .Boolean false) : ¬ a < b := by
  rw [term_lt_iff]
  cases a <;> cases b <;> simp_all [__eo_cmp]

theorem rat_zero_eq : native_mk_rational 0 1 = (0 : ℚ) := by
  simp [native_mk_rational]

/-- `__poly_add` keeps polynomials well formed, and adds no monomial above a bound
of both arguments. -/
theorem poly_add_wf : ∀ p q : Term, WfPoly p → WfPoly q → __poly_add p q ≠ .Stuck →
    WfPoly (__poly_add p q) ∧ ∀ b, (∀ e ∈ entries p, e.1 < b) → (∀ e ∈ entries q, e.1 < b) →
      ∀ e ∈ entries (__poly_add p q), e.1 < b := by
  intro p q hp hq h
  fun_induction __poly_add p q with
  | case1 => exact absurd rfl h
  | case2 => exact absurd rfl h
  | case3 a1 c1 p1 a2 c2 p2 v0 v1 v2 v3 v4 ih1 ih2 ih3 =>
    obtain ⟨hv1, ⟨q1, rfl, hq1⟩, hp1, hlt1⟩ := WfPoly.cons.1 hp
    obtain ⟨hv2, ⟨q2, rfl, hq2⟩, hp2, hlt2⟩ := WfPoly.cons.1 hq
    rcases ite_cases h with ⟨hc, e⟩ | ⟨hc, e⟩ <;> rw [e] at h ⊢
    · have ha1 : a1 ≠ .Stuck := by rintro rfl; simp [__eo_eq] at hc
      have ha2 : a2 ≠ .Stuck := by rintro rfl; cases a1 <;> simp [__eo_eq] at hc
      rw [eo_eq_of_ne ha1 ha2] at hc
      have ha : a2 = a1 := by simpa using hc
      subst ha
      rcases ite_cases h with ⟨_, e2⟩ | ⟨hz, e2⟩ <;> rw [e2] at h ⊢
      · obtain ⟨w, hb⟩ := ih1 hp1 hp2 h
        exact ⟨w, fun b hb1 hb2 => hb b (fun f hf => hb1 f (by simp [hf]))
          (fun f hf => hb2 f (by simp [hf]))⟩
      · obtain ⟨h1, h2, e3⟩ := mk_apply_of_ne h
        obtain ⟨-, h3, e4⟩ := mk_apply_of_ne h1
        obtain ⟨-, -, e5⟩ := mk_apply_of_ne h3
        obtain ⟨w, hb⟩ := ih1 hp1 hp2 h2
        have hv4 : v4 = .Rational (q1 + q2) := by simp [v4, __eo_add, native_qplus]
        have hne : q1 + q2 ≠ 0 := by
          intro h0; rw [hv4, h0, ← rat_zero_eq] at hz; simp [__eo_eq, native_teq] at hz
        rw [e3, e4, e5]
        refine ⟨WfPoly.cons.2 ⟨hv2, ⟨q1 + q2, hv4, hne⟩, w, hb a2 hlt1 hlt2⟩, ?_⟩
        intro b hb1 hb2 f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hb1 (a2, .Rational q1) List.mem_cons_self
        · exact hb b (fun g hg => hb1 g (by simp [hg])) (fun g hg => hb2 g (by simp [hg])) f hf
    · rcases ite_cases h with ⟨hc2, e2⟩ | ⟨hc2, e2⟩ <;> rw [e2] at h ⊢
      · -- `a2 < a1`: the head of `p` comes first.
        have hlt := cmp_true hc2
        obtain ⟨-, h2, e3⟩ := mk_apply_of_ne h
        have hq' : WfPoly (v2.Apply p2) := hq
        obtain ⟨w, hb⟩ := ih2 hp1 hq' h2
        rw [e3]
        refine ⟨WfPoly.cons.2 ⟨hv1, ⟨q1, rfl, hq1⟩, w, hb a1 hlt1 ?_⟩, ?_⟩
        · intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hlt
          · exact lt_trans (hlt2 f hf) hlt
        · intro b hb1 hb2 f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hb1 _ (by simp)
          · exact hb b (fun g hg => hb1 g (by simp [hg])) hb2 f hf
      · -- `a1 < a2`: the head of `q` comes first.
        have hne : a1 ≠ a2 := by
          intro e'; subst e'
          have ha1 : a1 ≠ .Stuck := by rintro rfl; exact hv1.1
          rw [eo_eq_of_ne ha1 ha1] at hc; simp at hc
        have hlt : a1 < a2 := lt_of_le_of_ne (not_lt.1 (cmp_false hc2)) hne
        obtain ⟨-, h2, e3⟩ := mk_apply_of_ne h
        have hp' : WfPoly (v1.Apply p1) := hp
        obtain ⟨w, hb⟩ := ih3 hp' hp2 h2
        rw [e3]
        refine ⟨WfPoly.cons.2 ⟨hv2, ⟨q2, rfl, hq2⟩, w, hb a2 ?_ hlt2⟩, ?_⟩
        · intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hlt
          · exact lt_trans (hlt1 f hf) hlt
        · intro b hb1 hb2 f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hb2 _ (by simp)
          · exact hb b hb1 (fun g hg => hb2 g (by simp [hg])) f hf
  | case4 p => exact ⟨hq, fun b _ hb2 => hb2⟩
  | case5 p _ => exact ⟨hp, fun b hb1 _ => hb1⟩
  | case6 => exact absurd rfl h

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder

theorem poly_neg_wf : ∀ p : Term, WfPoly p → __poly_neg p ≠ .Stuck →
    WfPoly (__poly_neg p) ∧ ∀ b, (∀ e ∈ entries p, e.1 < b) → ∀ e ∈ entries (__poly_neg p), e.1 < b := by
  intro p hp h
  fun_induction __poly_neg p with
  | case1 => exact ⟨WfPoly.zero, fun _ _ e he => by simp at he⟩
  | case2 a c p ih =>
    obtain ⟨hv, ⟨q, rfl, hq⟩, hp1, hlt⟩ := WfPoly.cons.1 hp
    obtain ⟨h1, h2, e1⟩ := mk_apply_of_ne h
    obtain ⟨-, h3, e2⟩ := mk_apply_of_ne h1
    obtain ⟨-, -, e3⟩ := mk_apply_of_ne h3
    obtain ⟨w, hb⟩ := ih hp1 h2
    rw [e1, e2, e3]
    refine ⟨WfPoly.cons.2 ⟨hv, ⟨-q, by simp [__eo_neg, native_qneg], neg_ne_zero.2 hq⟩, w, hb a hlt⟩, ?_⟩
    intro b hb1 f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hb1 (a, .Rational q) List.mem_cons_self
    · exact hb b (fun g hg => hb1 g (by simp [hg])) f hf
  | case3 p hp' => exact absurd rfl h

@[simp] theorem toL_nil : toL .__eo_List_nil = [] := rfl

theorem WfVars.nil : WfVars .__eo_List_nil := ⟨trivial, by simp⟩

theorem WfVars.cons {a l : Term} :
    WfVars (.Apply (.Apply .__eo_List_cons a) l) ↔ WfVars l ∧ ∀ x ∈ toL l, x ≤ a := by
  simp only [WfVars, IsVars, toL_cons, List.pairwise_cons, ge_iff_le]
  tauto

theorem mvar_mul_wf : ∀ a b : Term, WfVars a → WfVars b → __mvar_mul_mvar a b ≠ .Stuck →
    WfVars (__mvar_mul_mvar a b) ∧ ∀ u, (∀ x ∈ toL a, x ≤ u) → (∀ x ∈ toL b, x ≤ u) →
      ∀ x ∈ toL (__mvar_mul_mvar a b), x ≤ u := by
  intro a b ha hb h
  fun_induction __mvar_mul_mvar a b with
  | case1 => exact absurd rfl h
  | case2 => exact absurd rfl h
  | case3 a1 a2 c1 c2 v0 v1 ih1 ih2 =>
    obtain ⟨ha2, hle1⟩ := WfVars.cons.1 ha
    obtain ⟨hc2, hle2⟩ := WfVars.cons.1 hb
    rcases ite_cases h with ⟨hc, e⟩ | ⟨hc, e⟩ <;> rw [e] at h ⊢
    · have hlt := cmp_true hc
      obtain ⟨-, h2, e2⟩ := mk_apply_of_ne h
      obtain ⟨w, hbd⟩ := ih1 ha2 hb h2
      rw [e2]
      refine ⟨WfVars.cons.2 ⟨w, hbd a1 hle1 ?_⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_of_lt hlt
        · exact le_trans (hle2 x hx) (le_of_lt hlt)
      · intro u hu1 hu2 x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hu1 _ List.mem_cons_self
        · exact hbd u (fun y hy => hu1 y (List.mem_cons_of_mem _ hy)) hu2 x hx
    · have hle : a1 ≤ c1 := not_lt.1 (cmp_false hc)
      obtain ⟨-, h2, e2⟩ := mk_apply_of_ne h
      obtain ⟨w, hbd⟩ := ih2 ha hc2 h2
      rw [e2]
      refine ⟨WfVars.cons.2 ⟨w, hbd c1 ?_ hle2⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hle
        · exact le_trans (hle1 x hx) hle
      · intro u hu1 hu2 x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hu2 _ List.mem_cons_self
        · exact hbd u hu1 (fun y hy => hu2 y (List.mem_cons_of_mem _ hy)) x hx
  | case4 a2 _ => exact ⟨ha, fun u hu _ => hu⟩
  | case5 c2 _ _ => exact ⟨hb, fun u _ hu => hu⟩
  | case6 => exact absurd rfl h

/-- A well-formed monomial: well-formed variables and a nonzero rational coefficient. -/
def WfMon (m : Term) : Prop :=
  ∃ v c, m = .Apply (.Apply (.UOp UserOp._at__at_mon) v) c ∧ WfVars v ∧ ∃ q : ℚ, c = .Rational q ∧ q ≠ 0

theorem mon_mul_wf {m₁ m₂ : Term} (h1 : WfMon m₁) (h2 : WfMon m₂) (h : __mon_mul_mon m₁ m₂ ≠ .Stuck) :
    WfMon (__mon_mul_mon m₁ m₂) := by
  obtain ⟨v1, c1, rfl, hv1, q1, rfl, hq1⟩ := h1
  obtain ⟨v2, c2, rfl, hv2, q2, rfl, hq2⟩ := h2
  simp only [__mon_mul_mon] at h ⊢
  obtain ⟨h3, -, e1⟩ := mk_apply_of_ne h
  obtain ⟨-, h4, e2⟩ := mk_apply_of_ne h3
  rw [e1, e2]
  exact ⟨_, _, rfl, (mvar_mul_wf v1 v2 hv1 hv2 h4).1, q1 * q2,
    by simp [__eo_mul, native_qmult], mul_ne_zero hq1 hq2⟩

theorem WfPoly.single {m : Term} (hm : WfMon m) :
    WfPoly (.Apply (.Apply (.UOp UserOp._at__at_poly) m) (.UOp UserOp._at__at_poly_zero)) := by
  obtain ⟨v, c, rfl, hv, hc⟩ := hm
  exact WfPoly.cons.2 ⟨hv, hc, WfPoly.zero, by simp⟩

theorem WfPoly.of_poly {m p : Term} (h : WfPoly (.Apply (.Apply (.UOp UserOp._at__at_poly) m) p)) :
    WfMon m ∧ WfPoly p := by
  have hi := h.1
  unfold IsPoly at hi; split at hi
  · next v c q heq =>
    simp only [Term.Apply.injEq] at heq
    obtain ⟨⟨-, rfl⟩, rfl⟩ := heq
    obtain ⟨hv, hc, hp, -⟩ := WfPoly.cons.1 h
    exact ⟨⟨v, c, rfl, hv, hc⟩, hp⟩
  · next heq => cases heq
  · exact hi.elim

theorem poly_mul_mon_wf : ∀ m p : Term, WfMon m → WfPoly p → __poly_mul_mon m p ≠ .Stuck →
    WfPoly (__poly_mul_mon m p) := by
  intro m p hm hp h
  fun_induction __poly_mul_mon m p with
  | case1 => exact absurd rfl h
  | case2 m1 m2 p2 _ ih =>
    obtain ⟨hm2, hp2⟩ := WfPoly.of_poly hp
    obtain ⟨h1, h2⟩ := poly_add_args h
    obtain ⟨h3, -, e1⟩ := mk_apply_of_ne h1
    obtain ⟨-, h4, e2⟩ := mk_apply_of_ne h3
    have hs : WfPoly (__eo_mk_apply (__eo_mk_apply (.UOp UserOp._at__at_poly) (__mon_mul_mon m1 m2))
        (.UOp UserOp._at__at_poly_zero)) := by
      rw [e1, e2]; exact WfPoly.single (mon_mul_wf hm hm2 h4)
    exact (poly_add_wf _ _ hs (ih hm hp2 h2) h).1
  | case3 => exact WfPoly.zero
  | case4 => exact absurd rfl h

theorem poly_mul_wf : ∀ p q : Term, WfPoly p → WfPoly q → __poly_mul p q ≠ .Stuck →
    WfPoly (__poly_mul p q) := by
  intro p q hp hq h
  fun_induction __poly_mul p q with
  | case1 => exact absurd rfl h
  | case2 => exact absurd rfl h
  | case3 m p1 p _ ih =>
    obtain ⟨hm, hp1⟩ := WfPoly.of_poly hp
    obtain ⟨h1, h2⟩ := poly_add_args h
    exact (poly_add_wf _ _ (poly_mul_mon_wf _ _ hm hq h1) (ih hp1 hq h2) h).1
  | case4 => exact WfPoly.zero
  | case5 => exact WfPoly.zero
  | case6 => exact absurd rfl h

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder

theorem poly_neg_arg {p : Term} (h : __poly_neg p ≠ .Stuck) : p ≠ .Stuck := by
  rintro rfl; simp [__poly_neg] at h

theorem poly_mul_args {p q : Term} (h : __poly_mul p q ≠ .Stuck) : p ≠ .Stuck ∧ q ≠ .Stuck := by
  constructor <;> rintro rfl
  · simp [__poly_mul] at h
  · cases p <;> simp [__poly_mul] at h

theorem poly_mul_mon_arg {m p : Term} (h : __poly_mul_mon m p ≠ .Stuck) : p ≠ .Stuck := by
  rintro rfl; cases m <;> simp [__poly_mul_mon] at h

theorem is_q_true {v : Term} (h : __eo_is_q v = .Boolean true) : ∃ q, v = .Rational q := by
  cases v <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]

theorem not_eq_true {v w : Term} (hw : w ≠ .Stuck) (h : __eo_not (__eo_eq v w) = .Boolean true) :
    v ≠ w := by
  rintro rfl
  cases v <;> simp_all [__eo_not, __eo_eq, native_teq, native_not]

theorem is_eq_false {v w : Term} (_hv : v ≠ .Stuck) (_hw : w ≠ .Stuck)
    (h : __eo_is_eq v w = .Boolean false) : v ≠ w := by
  rintro rfl; simp_all [__eo_is_eq, native_and, native_not, native_teq]

theorem WfVars.single (a : Term) : WfVars (.Apply (.Apply .__eo_List_cons a) .__eo_List_nil) :=
  WfVars.cons.2 ⟨WfVars.nil, by simp⟩

theorem WfPoly.atom (t : Term) :
    WfPoly (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon)
      (.Apply (.Apply .__eo_List_cons t) .__eo_List_nil)) (.Rational (native_mk_rational 1 1))))
      (.UOp UserOp._at__at_poly_zero)) :=
  WfPoly.single ⟨_, _, rfl, WfVars.single t, _, rfl, by simp [native_mk_rational]⟩

/-- The constant monomial `1/q` of a division by a nonzero constant `q`. -/
theorem wfMon_qdiv {v : Term}
    (hc : __eo_ite (__eo_is_q v) (__eo_not (__eo_eq v (.Rational (native_mk_rational 0 1))))
      (.Boolean false) = .Boolean true)
    (h : __eo_mk_apply (.Apply (.UOp UserOp._at__at_mon) .__eo_List_nil)
      (__eo_qdiv (.Rational (native_mk_rational 1 1)) v) ≠ .Stuck) :
    WfMon (__eo_mk_apply (.Apply (.UOp UserOp._at__at_mon) .__eo_List_nil)
      (__eo_qdiv (.Rational (native_mk_rational 1 1)) v)) := by
  have hq : __eo_is_q v = .Boolean true := by
    rcases ite_cases (show __eo_ite (__eo_is_q v) _ (.Boolean false) ≠ .Stuck by rw [hc]; simp)
      with ⟨h1, -⟩ | ⟨-, e⟩
    · exact h1
    · rw [e] at hc; cases hc
  obtain ⟨q, rfl⟩ := is_q_true hq
  have hne : q ≠ 0 := by
    have hn : __eo_not (__eo_eq (.Rational q) (.Rational (native_mk_rational 0 1))) = .Boolean true := by
      simpa [__eo_ite, native_ite, native_teq, hq] using hc
    have := not_eq_true (by simp) hn
    rw [rat_zero_eq] at this; simpa using this
  obtain ⟨-, -, e⟩ := mk_apply_of_ne h
  rw [e]
  refine ⟨_, _, rfl, WfVars.nil, 1 / q, ?_, by simpa using hne⟩
  simp [__eo_qdiv, native_ite, native_qeq, native_qdiv_total, native_mk_rational, hne, Ne.symm hne]

theorem get_norm_wf : ∀ t : Term, __get_arith_poly_norm t ≠ .Stuck → WfPoly (__get_arith_poly_norm t) := by
  intro t h
  fun_induction __get_arith_poly_norm t with
  | case1 => exact absurd rfl h
  | case2 a ih => exact (poly_neg_wf _ (ih (poly_neg_arg h)) h).1
  | case3 a b iha ihb =>
    obtain ⟨h1, h2⟩ := poly_add_args h
    exact (poly_add_wf _ _ (iha h1) (ihb h2) h).1
  | case4 a b iha ihb =>
    obtain ⟨h1, h2⟩ := poly_add_args h
    exact (poly_add_wf _ _ (iha h1) (poly_neg_wf _ (ihb (poly_neg_arg h2)) h2).1 h).1
  | case5 a b iha ihb =>
    obtain ⟨h1, h2⟩ := poly_mul_args h
    exact poly_mul_wf _ _ (iha h1) (ihb h2) h
  | case6 a b v0 ih | case7 a b v0 ih =>
    rcases ite_cases h with ⟨hc, e⟩ | ⟨_, e⟩ <;> rw [e] at h ⊢
    · have hm := wfMon_qdiv hc (by intro hs; rw [hs] at h; simp [__poly_mul_mon] at h)
      exact poly_mul_mon_wf _ _ hm (ih (poly_mul_mon_arg h)) h
    · exact WfPoly.atom _
  | case8 a ih => exact ih h
  | case9 a _ _ _ _ _ _ _ _ v0 =>
    rcases ite_cases h with ⟨hc, e⟩ | ⟨_, e⟩ <;> rw [e] at h ⊢
    · obtain ⟨q, hq⟩ := is_q_true hc
      rcases ite_cases h with ⟨_, e2⟩ | ⟨hz, e2⟩ <;> rw [e2] at h ⊢
      · exact WfPoly.zero
      · have hne : v0 ≠ .Rational (native_mk_rational 0 1) := is_eq_false (by rw [hq]; simp) (by simp) hz
        obtain ⟨h1, -, e3⟩ := mk_apply_of_ne h
        obtain ⟨-, h2, e4⟩ := mk_apply_of_ne h1
        obtain ⟨-, -, e5⟩ := mk_apply_of_ne h2
        rw [e3, e4, e5]
        refine WfPoly.single ⟨_, _, rfl, WfVars.nil, q, hq, ?_⟩
        rintro rfl; rw [hq, rat_zero_eq] at hne; exact hne rfl
    · exact WfPoly.atom _

/-- **Logos's normal form is canonical**: two terms whose normal forms have the
same value have the same normal form. -/
theorem get_norm_eq_of_polyVal_eq {a b : Term} (ha : __get_arith_poly_norm a ≠ .Stuck)
    (hb : __get_arith_poly_norm b ≠ .Stuck)
    (h : polyVal (__get_arith_poly_norm a) = polyVal (__get_arith_poly_norm b)) :
    __get_arith_poly_norm a = __get_arith_poly_norm b :=
  (get_norm_wf a ha).eq_of_polyVal_eq (get_norm_wf b hb) h

end Telos.PolyNorm
