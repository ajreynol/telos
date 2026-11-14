import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Cpc.Logos
import Cpc.SmtTranslate
import Telos.Arith.PolyNorm
import Telos.Rewriter.Certified
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
whatever algorithm, produces equations `arith_poly_norm` accepts. The rest of the
file shows this of telos's normalizer `arithNorm` (`Telos/Arith/PolyNorm.lean`):

* The normal form of a term of type `Int` or `Real` is not stuck
  (`get_norm_ne_stuck`).
* `V t` is the value of `t`'s normal form. For the operators telos decomposes,
  it is computed from the values of the arguments (`V_plus`, …), and for `+` and
  `*` through their typed nils (`V_chain_plus`, `V_typedNil_plus`, …).
* `embedT` is the value of a telos polynomial, its leaves read by `V`. telos's
  polynomial operations are ring operations on it (`add_val`, `mul_val`, …),
  `polyOf` has the value of its node (`polyOf_val`), and rendering keeps the
  value (`V_toNode`).
* Hence `n` and `arithNorm n` have the same normal form (`arithNorm_get_norm`),
  and the one-step command list `arith_poly_norm` proves `(= n (arithNorm n))`
  (`arithNorm_provesEq_of_typeof`, completed in `ArithNorm.lean`).
-/
set_option linter.internalConstructors false
-- Proof-script lints: these proofs are checked, not style-reviewed.
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

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

/-- `v` is an `eo` list of (non-stuck) variables. -/
def IsVars : Term → Prop
  | .Apply (.Apply .__eo_List_cons a) l => a ≠ .Stuck ∧ IsVars l
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
      rw [h.1, ih hv.2 hw.2 h.2]
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
    WfVars (.Apply (.Apply .__eo_List_cons a) l) ↔ a ≠ .Stuck ∧ WfVars l ∧ ∀ x ∈ toL l, x ≤ a := by
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
    obtain ⟨ha1, ha2, hle1⟩ := WfVars.cons.1 ha
    obtain ⟨hc1, hc2, hle2⟩ := WfVars.cons.1 hb
    rcases ite_cases h with ⟨hc, e⟩ | ⟨hc, e⟩ <;> rw [e] at h ⊢
    · have hlt := cmp_true hc
      obtain ⟨-, h2, e2⟩ := mk_apply_of_ne h
      obtain ⟨w, hbd⟩ := ih1 ha2 hb h2
      rw [e2]
      refine ⟨WfVars.cons.2 ⟨ha1, w, hbd a1 hle1 ?_⟩, ?_⟩
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
      refine ⟨WfVars.cons.2 ⟨hc1, w, hbd c1 ?_ hle2⟩, ?_⟩
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

theorem WfVars.single {a : Term} (ha : a ≠ .Stuck) :
    WfVars (.Apply (.Apply .__eo_List_cons a) .__eo_List_nil) :=
  WfVars.cons.2 ⟨ha, WfVars.nil, by simp⟩

theorem WfPoly.atom {t : Term} (ht : t ≠ .Stuck) :
    WfPoly (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon)
      (.Apply (.Apply .__eo_List_cons t) .__eo_List_nil)) (.Rational (native_mk_rational 1 1))))
      (.UOp UserOp._at__at_poly_zero)) :=
  WfPoly.single ⟨_, _, rfl, WfVars.single ht, _, rfl, by simp [native_mk_rational]⟩

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
    · exact WfPoly.atom (by simp)
  | case8 a ih => exact ih h
  | case9 a hs _ _ _ _ _ _ _ v0 =>
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
    · exact WfPoly.atom hs

/-- **Logos's normal form is canonical**: two terms whose normal forms have the
same value have the same normal form. -/
theorem get_norm_eq_of_polyVal_eq {a b : Term} (ha : __get_arith_poly_norm a ≠ .Stuck)
    (hb : __get_arith_poly_norm b ≠ .Stuck)
    (h : polyVal (__get_arith_poly_norm a) = polyVal (__get_arith_poly_norm b)) :
    __get_arith_poly_norm a = __get_arith_poly_norm b :=
  (get_norm_wf a ha).eq_of_polyVal_eq (get_norm_wf b hb) h

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm

/-! ## The normal form of an arithmetic term is not stuck -/

theorem mk_apply_eq {f x : Term} (hf : f ≠ .Stuck) (hx : x ≠ .Stuck) :
    __eo_mk_apply f x = .Apply f x := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

theorem mk_apply_ne_stuck {f x : Term} (hf : f ≠ .Stuck) (hx : x ≠ .Stuck) :
    __eo_mk_apply f x ≠ .Stuck := by
  rw [mk_apply_eq hf hx]; simp

theorem ite_true (x y : Term) : __eo_ite (.Boolean true) x y = x := by
  simp [__eo_ite, native_ite, native_teq]

theorem ite_false (x y : Term) : __eo_ite (.Boolean false) x y = y := by
  simp [__eo_ite, native_ite, native_teq]

theorem IsVars.ne_stuck {v : Term} (h : IsVars v) : v ≠ .Stuck := by
  rintro rfl; exact h

theorem cmp_eq (a b : Term) (ha : a ≠ .Stuck) (hb : b ≠ .Stuck) :
    __eo_cmp a b = .Boolean (native_tcmp a b) := by
  cases a <;> cases b <;> simp_all [__eo_cmp]

theorem isPoly_cases {p : Term} (h : IsPoly p) :
    p = .UOp UserOp._at__at_poly_zero ∨
      ∃ v c r, p = .Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon) v) c)) r := by
  unfold IsPoly at h; split at h
  · exact Or.inr ⟨_, _, _, rfl⟩
  · exact Or.inl rfl
  · exact h.elim

theorem poly_add_ne_stuck : ∀ p q : Term, WfPoly p → WfPoly q → __poly_add p q ≠ .Stuck := by
  intro p q hp hq
  fun_induction __poly_add p q with
  | case1 => exact absurd hp.1 (by simp [IsPoly])
  | case2 => exact absurd hq.1 (by simp [IsPoly])
  | case3 a1 c1 p1 a2 c2 p2 v0 v1 v2 v3 v4 ih1 ih2 ih3 =>
    obtain ⟨hv1, ⟨q1, rfl, hq1⟩, hp1, hlt1⟩ := WfPoly.cons.1 hp
    obtain ⟨hv2, ⟨q2, rfl, hq2⟩, hp2, hlt2⟩ := WfPoly.cons.1 hq
    have ha1 := hv1.1.ne_stuck
    have ha2 := hv2.1.ne_stuck
    rw [eo_eq_of_ne ha1 ha2]
    by_cases e : a2 = a1
    · subst e
      have hv4 : v4 = .Rational (q1 + q2) := by simp [v4, __eo_add, native_qplus]
      simp only [decide_true, ite_true]
      rw [eo_eq_of_ne (by rw [hv4]; simp) (by simp)]
      by_cases hz : Term.Rational (native_mk_rational 0 1) = v4
      · simp only [hz, decide_true, ite_true]; exact ih1 hp1 hp2
      · simp only [hz, decide_false, ite_false]
        refine mk_apply_ne_stuck (mk_apply_ne_stuck (by simp) (mk_apply_ne_stuck (by simp [v0])
          (by rw [hv4]; simp))) (ih1 hp1 hp2)
    · simp only [e, decide_false, ite_false]
      rw [cmp_eq _ _ ha2 ha1]
      cases native_tcmp a2 a1
      · rw [ite_false]; exact mk_apply_ne_stuck (by simp [v2]) (ih3 hp hp2)
      · rw [ite_true]; exact mk_apply_ne_stuck (by simp [v1]) (ih2 hp1 hq)
  | case4 p => exact fun h => by subst h; exact hq.1
  | case5 p _ => exact fun h => by subst h; exact hp.1
  | case6 p q _ _ hcc hzp hzq =>
    exfalso
    rcases isPoly_cases hp.1 with rfl | ⟨v, c, r, rfl⟩
    · exact hzp rfl
    · rcases isPoly_cases hq.1 with rfl | ⟨w, d, t, rfl⟩
      · exact hzq rfl
      · exact hcc v c r w d t rfl rfl

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm

theorem poly_neg_ne_stuck : ∀ p : Term, WfPoly p → __poly_neg p ≠ .Stuck := by
  intro p hp
  fun_induction __poly_neg p with
  | case1 => simp
  | case2 a c p ih =>
    obtain ⟨-, ⟨q, rfl, -⟩, hp1, -⟩ := WfPoly.cons.1 hp
    exact mk_apply_ne_stuck (mk_apply_ne_stuck (by simp)
      (mk_apply_ne_stuck (by simp) (by simp [__eo_neg]))) (ih hp1)
  | case3 p hz hc =>
    exfalso
    rcases isPoly_cases hp.1 with rfl | ⟨v, c, r, rfl⟩
    · exact hz rfl
    · exact hc v c r rfl

theorem isVars_cases {v : Term} (h : IsVars v) :
    v = .__eo_List_nil ∨ ∃ a l, v = .Apply (.Apply .__eo_List_cons a) l := by
  unfold IsVars at h; split at h
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl
  · exact h.elim

theorem mvar_mul_ne_stuck : ∀ a b : Term, WfVars a → WfVars b → __mvar_mul_mvar a b ≠ .Stuck := by
  intro a b ha hb
  fun_induction __mvar_mul_mvar a b with
  | case1 => exact absurd ha.1 (by simp [IsVars])
  | case2 => exact absurd hb.1 (by simp [IsVars])
  | case3 a1 a2 c1 c2 v0 v1 ih1 ih2 =>
    obtain ⟨ha1, ha2, -⟩ := WfVars.cons.1 ha
    obtain ⟨hc1, hc2, -⟩ := WfVars.cons.1 hb
    rw [cmp_eq _ _ hc1 ha1]
    cases native_tcmp c1 a1
    · rw [ite_false]; exact mk_apply_ne_stuck (by simp [v1]) (ih2 ha hc2)
    · rw [ite_true]; exact mk_apply_ne_stuck (by simp [v0]) (ih1 ha2 hb)
  | case4 a2 _ => exact ha.1.ne_stuck
  | case5 c2 _ _ => exact hb.1.ne_stuck
  | case6 a b _ _ hcc hnb hna =>
    exfalso
    rcases isVars_cases ha.1 with rfl | ⟨x, l, rfl⟩
    · exact hna rfl
    · rcases isVars_cases hb.1 with rfl | ⟨y, m, rfl⟩
      · exact hnb rfl
      · exact hcc x l y m rfl rfl

theorem mon_mul_ne_stuck {m₁ m₂ : Term} (h1 : WfMon m₁) (h2 : WfMon m₂) : __mon_mul_mon m₁ m₂ ≠ .Stuck := by
  obtain ⟨v1, c1, rfl, hv1, q1, rfl, -⟩ := h1
  obtain ⟨v2, c2, rfl, hv2, q2, rfl, -⟩ := h2
  simp only [__mon_mul_mon]
  exact mk_apply_ne_stuck (mk_apply_ne_stuck (by simp) (mvar_mul_ne_stuck _ _ hv1 hv2))
    (by simp [__eo_mul])

theorem poly_mul_mon_ne_stuck : ∀ m p : Term, WfMon m → WfPoly p → __poly_mul_mon m p ≠ .Stuck := by
  intro m p hm hp
  fun_induction __poly_mul_mon m p with
  | case1 => obtain ⟨_, _, h, -⟩ := hm; cases h
  | case2 m1 m2 p2 _ ih =>
    obtain ⟨hm2, hp2⟩ := WfPoly.of_poly hp
    have h4 := mon_mul_ne_stuck hm hm2
    have hs : WfPoly (__eo_mk_apply (__eo_mk_apply (.UOp UserOp._at__at_poly) (__mon_mul_mon m1 m2))
        (.UOp UserOp._at__at_poly_zero)) := by
      rw [mk_apply_eq (by simp) h4, mk_apply_eq (by simp) (by simp)]
      exact WfPoly.single (mon_mul_wf hm hm2 h4)
    exact poly_add_ne_stuck _ _ hs (poly_mul_mon_wf _ _ hm hp2 (ih hm hp2))
  | case3 => simp
  | case4 m p =>
    exfalso
    rcases isPoly_cases hp.1 with rfl | ⟨v, c, r, rfl⟩ <;> simp_all

theorem poly_mul_ne_stuck : ∀ p q : Term, WfPoly p → WfPoly q → __poly_mul p q ≠ .Stuck := by
  intro p q hp hq
  fun_induction __poly_mul p q with
  | case1 => exact absurd hp.1 (by simp [IsPoly])
  | case2 => exact absurd hq.1 (by simp [IsPoly])
  | case3 m p1 p _ ih =>
    obtain ⟨hm, hp1⟩ := WfPoly.of_poly hp
    exact poly_add_ne_stuck _ _ (poly_mul_mon_wf _ _ hm hq (poly_mul_mon_ne_stuck _ _ hm hq))
      (poly_mul_wf _ _ hp1 hq (ih hp1 hq))
  | case4 => simp
  | case5 => simp
  | case6 p q =>
    exfalso
    rcases isPoly_cases hp.1 with rfl | ⟨v, c, r, rfl⟩ <;>
      rcases isPoly_cases hq.1 with rfl | ⟨w, d, t, rfl⟩ <;> simp_all

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm

/-- The SMT type of a term's translation. -/
def smtty (t : Term) : SmtType := __smtx_typeof (__eo_to_smt t)

/-- An arithmetic type. -/
def ArithTy (T : SmtType) : Prop := T = .Int ∨ T = .Real

theorem smtty_stuck : smtty .Stuck = .None := by
  unfold smtty; rw [show __eo_to_smt .Stuck = SmtTerm.None from rfl]
  rw [__smtx_typeof.eq_def]

theorem smtty_uneg (a : Term) : smtty (.Apply (.UOp .__eoo_neg_2) a) =
    __smtx_typeof_arith_overload_op_1 (smtty a) := by
  unfold smtty; rw [show __eo_to_smt (.Apply (.UOp .__eoo_neg_2) a) = SmtTerm.uneg (__eo_to_smt a) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtty_plus (a b : Term) : smtty (.Apply (.Apply (.UOp .plus) a) b) =
    __smtx_typeof_arith_overload_op_2 (smtty a) (smtty b) := by
  unfold smtty
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .plus) a) b) = SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtty_neg (a b : Term) : smtty (.Apply (.Apply (.UOp .neg) a) b) =
    __smtx_typeof_arith_overload_op_2 (smtty a) (smtty b) := by
  unfold smtty
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .neg) a) b) = SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtty_mult (a b : Term) : smtty (.Apply (.Apply (.UOp .mult) a) b) =
    __smtx_typeof_arith_overload_op_2 (smtty a) (smtty b) := by
  unfold smtty
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .mult) a) b) = SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtty_qdiv (a b : Term) : smtty (.Apply (.Apply (.UOp .qdiv) a) b) =
    __smtx_typeof_arith_overload_op_2_ret (smtty a) (smtty b) .Real := by
  unfold smtty
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .qdiv) a) b) = SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtty_qdiv_total (a b : Term) : smtty (.Apply (.Apply (.UOp .qdiv_total) a) b) =
    __smtx_typeof_arith_overload_op_2_ret (smtty a) (smtty b) .Real := by
  unfold smtty
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .qdiv_total) a) b) =
    SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtty_to_real (a : Term) : smtty (.Apply (.UOp .to_real) a) =
    native_ite (native_Teq (smtty a) .Int) .Real .None := by
  unfold smtty; rw [show __eo_to_smt (.Apply (.UOp .to_real) a) = SmtTerm.to_real (__eo_to_smt a) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem arith_op_1_inv {T : SmtType} (h : ArithTy (__smtx_typeof_arith_overload_op_1 T)) : ArithTy T := by
  unfold ArithTy at *; cases T <;> simp_all [__smtx_typeof_arith_overload_op_1]

theorem arith_op_2_inv {T U : SmtType} (h : ArithTy (__smtx_typeof_arith_overload_op_2 T U)) :
    ArithTy T ∧ ArithTy U := by
  unfold ArithTy at *; cases T <;> cases U <;> simp_all [__smtx_typeof_arith_overload_op_2]

theorem arith_op_2_ret_inv {T U : SmtType} (h : ArithTy (__smtx_typeof_arith_overload_op_2_ret T U .Real)) :
    ArithTy T ∧ ArithTy U := by
  unfold ArithTy at *; cases T <;> cases U <;> simp_all [__smtx_typeof_arith_overload_op_2_ret]

theorem to_real_inv {T : SmtType} (h : ArithTy (native_ite (native_Teq T .Int) .Real .None)) : ArithTy T := by
  unfold ArithTy at *; cases T <;> simp_all [native_ite, native_Teq]

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm

theorem is_q_bool (v : Term) : ∃ b, __eo_is_q v = .Boolean b := ⟨_, rfl⟩

theorem is_eq_bool (v w : Term) : ∃ b, __eo_is_eq v w = .Boolean b := ⟨_, rfl⟩

/-- The condition of a division by a constant is a Boolean. -/
theorem qdiv_cond_bool (v : Term) :
    ∃ b, __eo_ite (__eo_is_q v) (__eo_not (__eo_eq v (.Rational (native_mk_rational 0 1))))
      (.Boolean false) = .Boolean b := by
  obtain ⟨b, hb⟩ := is_q_bool v
  rw [hb]; cases b
  · exact ⟨false, ite_false _ _⟩
  · obtain ⟨q, rfl⟩ := is_q_true hb
    rw [ite_true, eo_eq_of_ne (by simp) (by simp)]
    exact ⟨_, rfl⟩

theorem qdiv_cond_true {v : Term}
    (hc : __eo_ite (__eo_is_q v) (__eo_not (__eo_eq v (.Rational (native_mk_rational 0 1))))
      (.Boolean false) = .Boolean true) : ∃ q : ℚ, v = .Rational q ∧ q ≠ 0 := by
  obtain ⟨b, hb⟩ := is_q_bool v
  rw [hb] at hc; cases b
  · rw [ite_false] at hc; cases hc
  · obtain ⟨q, rfl⟩ := is_q_true hb
    rw [ite_true] at hc
    refine ⟨q, rfl, ?_⟩
    have := not_eq_true (by simp) hc
    rintro rfl; exact this (by rw [rat_zero_eq])

/-- **The normal form of an arithmetic term is not stuck.** -/
theorem get_norm_ne_stuck : ∀ t : Term, ArithTy (smtty t) → __get_arith_poly_norm t ≠ .Stuck := by
  intro t ht
  fun_induction __get_arith_poly_norm t with
  | case1 => rw [smtty_stuck] at ht; rcases ht with h | h <;> cases h
  | case2 a ih =>
    rw [smtty_uneg] at ht
    have h := ih (arith_op_1_inv ht)
    exact poly_neg_ne_stuck _ (get_norm_wf a h)
  | case3 a b iha ihb =>
    rw [smtty_plus] at ht
    obtain ⟨h1, h2⟩ := arith_op_2_inv ht
    exact poly_add_ne_stuck _ _ (get_norm_wf a (iha h1)) (get_norm_wf b (ihb h2))
  | case4 a b iha ihb =>
    rw [smtty_neg] at ht
    obtain ⟨h1, h2⟩ := arith_op_2_inv ht
    have hb := get_norm_wf b (ihb h2)
    exact poly_add_ne_stuck _ _ (get_norm_wf a (iha h1))
      ((poly_neg_wf _ hb (poly_neg_ne_stuck _ hb)).1)
  | case5 a b iha ihb =>
    rw [smtty_mult] at ht
    obtain ⟨h1, h2⟩ := arith_op_2_inv ht
    exact poly_mul_ne_stuck _ _ (get_norm_wf a (iha h1)) (get_norm_wf b (ihb h2))
  | case6 a b v0 ih | case7 a b v0 ih =>
    first | rw [smtty_qdiv] at ht | rw [smtty_qdiv_total] at ht
    obtain ⟨h1, -⟩ := arith_op_2_ret_inv ht
    obtain ⟨c, hc⟩ := qdiv_cond_bool v0
    rw [hc]; cases c
    · rw [ite_false]; simp
    · rw [ite_true]
      have hm : __eo_mk_apply (.Apply (.UOp UserOp._at__at_mon) .__eo_List_nil)
          (__eo_qdiv (.Rational (native_mk_rational 1 1)) v0) ≠ .Stuck := by
        obtain ⟨q, hq, hq0⟩ := qdiv_cond_true hc
        rw [hq]
        refine mk_apply_ne_stuck (by simp) ?_
        simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq0]
      have hwm := wfMon_qdiv hc hm
      exact poly_mul_mon_ne_stuck _ _ hwm (get_norm_wf a (ih h1))
  | case8 a ih =>
    rw [smtty_to_real] at ht
    exact ih (to_real_inv ht)
  | case9 a hs _ _ _ _ _ _ _ v0 =>
    obtain ⟨c, hc⟩ := is_q_bool v0
    rw [hc]; cases c
    · rw [ite_false]; simp
    · rw [ite_true]
      obtain ⟨q, hq⟩ := is_q_true hc
      obtain ⟨d, hd⟩ := is_eq_bool v0 (.Rational (native_mk_rational 0 1))
      rw [hd]; cases d
      · rw [ite_false]
        exact mk_apply_ne_stuck (mk_apply_ne_stuck (by simp)
          (mk_apply_ne_stuck (by simp) (by rw [hq]; simp))) (by simp)
      · rw [ite_true]; simp

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm

/-! ## Values of normal forms, operator by operator -/

/-- The value of a term's normal form. -/
noncomputable def V (t : Term) : P := polyVal (__get_arith_poly_norm t)

/-- `t`'s normal form is not stuck. -/
def NS (t : Term) : Prop := __get_arith_poly_norm t ≠ .Stuck

theorem gn_plus (a b : Term) : __get_arith_poly_norm (.Apply (.Apply (.UOp .plus) a) b) =
    __poly_add (__get_arith_poly_norm a) (__get_arith_poly_norm b) := by
  rw [__get_arith_poly_norm]

theorem V_plus {a b : Term} (h : NS (.Apply (.Apply (.UOp .plus) a) b)) :
    NS a ∧ NS b ∧ V (.Apply (.Apply (.UOp .plus) a) b) = V a + V b := by
  unfold NS at h; rw [gn_plus] at h
  obtain ⟨h1, h2⟩ := poly_add_args h
  exact ⟨h1, h2, by unfold V; rw [gn_plus, polyVal_add _ _ h]⟩

theorem V_sub {a b : Term} (h : NS (.Apply (.Apply (.UOp .neg) a) b)) :
    NS a ∧ NS b ∧ V (.Apply (.Apply (.UOp .neg) a) b) = V a - V b := by
  unfold NS at h; rw [__get_arith_poly_norm] at h
  obtain ⟨h1, h2⟩ := poly_add_args h
  refine ⟨h1, poly_neg_arg h2, ?_⟩
  unfold V; rw [__get_arith_poly_norm, polyVal_add _ _ h, polyVal_neg _ h2]; ring

theorem V_mult {a b : Term} (h : NS (.Apply (.Apply (.UOp .mult) a) b)) :
    NS a ∧ NS b ∧ V (.Apply (.Apply (.UOp .mult) a) b) = V a * V b := by
  unfold NS at h; rw [__get_arith_poly_norm] at h
  obtain ⟨h1, h2⟩ := poly_mul_args h
  exact ⟨h1, h2, by unfold V; rw [__get_arith_poly_norm, polyVal_mul _ _ h]⟩

theorem V_uneg {a : Term} (h : NS (.Apply (.UOp .__eoo_neg_2) a)) :
    NS a ∧ V (.Apply (.UOp .__eoo_neg_2) a) = - V a := by
  unfold NS at h; rw [__get_arith_poly_norm] at h
  exact ⟨poly_neg_arg h, by unfold V; rw [__get_arith_poly_norm, polyVal_neg _ h]⟩

theorem V_to_real {a : Term} (h : NS (.Apply (.UOp .to_real) a)) :
    NS a ∧ V (.Apply (.UOp .to_real) a) = V a := by
  unfold NS at h; rw [__get_arith_poly_norm] at h
  exact ⟨h, by unfold V; rw [__get_arith_poly_norm]⟩

/-- The condition of a division by the nonzero rational `q` holds. -/
theorem qdiv_cond_rat {q : ℚ} (hq : q ≠ 0) :
    __eo_ite (__eo_is_q (.Rational q)) (__eo_not (__eo_eq (.Rational q) (.Rational (native_mk_rational 0 1))))
      (.Boolean false) = .Boolean true := by
  rw [show __eo_is_q (.Rational q) = .Boolean true by simp [__eo_is_q, __eo_is_q_internal, native_and,
    native_not, native_teq], ite_true, eo_eq_of_ne (by simp) (by simp)]
  simp [__eo_not, native_not, rat_zero_eq, Ne.symm hq]

theorem V_qdiv_rat {a : Term} {q : ℚ} (hq : q ≠ 0) (h : NS (.Apply (.Apply (.UOp .qdiv) a) (.Rational q))) :
    NS a ∧ V (.Apply (.Apply (.UOp .qdiv) a) (.Rational q)) = C (1 / q) * V a := by
  unfold NS at h; rw [__get_arith_poly_norm] at h
  simp only [__eo_to_q] at h
  rw [qdiv_cond_rat hq, ite_true] at h
  refine ⟨poly_mul_mon_arg h, ?_⟩
  unfold V; rw [__get_arith_poly_norm]; simp only [__eo_to_q]
  rw [qdiv_cond_rat hq, ite_true, polyVal_mul_mon _ _ h]
  rw [mk_apply_eq (by simp) (by simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq])]
  simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq, native_qdiv_total, coeffOf]

theorem V_qdiv_total_rat {a : Term} {q : ℚ} (hq : q ≠ 0)
    (h : NS (.Apply (.Apply (.UOp .qdiv_total) a) (.Rational q))) :
    NS a ∧ V (.Apply (.Apply (.UOp .qdiv_total) a) (.Rational q)) = C (1 / q) * V a := by
  unfold NS at h; rw [__get_arith_poly_norm] at h
  simp only [__eo_to_q] at h
  rw [qdiv_cond_rat hq, ite_true] at h
  refine ⟨poly_mul_mon_arg h, ?_⟩
  unfold V; rw [__get_arith_poly_norm]; simp only [__eo_to_q]
  rw [qdiv_cond_rat hq, ite_true, polyVal_mul_mon _ _ h]
  rw [mk_apply_eq (by simp) (by simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq])]
  simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq, native_qdiv_total, coeffOf]

theorem V_qdiv_num {a : Term} {i : Int} (hi : i ≠ 0) (h : NS (.Apply (.Apply (.UOp .qdiv) a) (.Numeral i))) :
    NS a ∧ V (.Apply (.Apply (.UOp .qdiv) a) (.Numeral i)) = C (1 / (i : ℚ)) * V a := by
  have hq : (i : ℚ) ≠ 0 := by exact_mod_cast hi
  have e : __eo_to_q (.Numeral i) = .Rational (i : ℚ) := by
    simp [__eo_to_q, native_to_real, native_mk_rational]
  unfold NS at h; rw [__get_arith_poly_norm] at h
  rw [e, qdiv_cond_rat hq, ite_true] at h
  refine ⟨poly_mul_mon_arg h, ?_⟩
  unfold V; rw [__get_arith_poly_norm, e, qdiv_cond_rat hq, ite_true, polyVal_mul_mon _ _ h]
  rw [mk_apply_eq (by simp) (by simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq])]
  simp [__eo_qdiv, native_ite, native_qeq, native_mk_rational, Ne.symm hq, native_qdiv_total, coeffOf]

theorem gn_rational (q : ℚ) : __get_arith_poly_norm (.Rational q) =
    __eo_ite (__eo_is_q (.Rational q))
      (__eo_ite (__eo_is_eq (.Rational q) (.Rational (native_mk_rational 0 1))) (.UOp UserOp._at__at_poly_zero)
        (__eo_mk_apply (__eo_mk_apply (.UOp UserOp._at__at_poly)
          (__eo_mk_apply (.Apply (.UOp UserOp._at__at_mon) .__eo_List_nil) (.Rational q)))
          (.UOp UserOp._at__at_poly_zero)))
      (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon)
        (.Apply (.Apply .__eo_List_cons (.Rational q)) .__eo_List_nil)) (.Rational (native_mk_rational 1 1))))
        (.UOp UserOp._at__at_poly_zero)) := by
  rw [__get_arith_poly_norm] <;> simp [__eo_to_q]

theorem gn_numeral (i : Int) : __get_arith_poly_norm (.Numeral i) =
    __eo_ite (__eo_is_q (.Rational (i : ℚ)))
      (__eo_ite (__eo_is_eq (.Rational (i : ℚ)) (.Rational (native_mk_rational 0 1))) (.UOp UserOp._at__at_poly_zero)
        (__eo_mk_apply (__eo_mk_apply (.UOp UserOp._at__at_poly)
          (__eo_mk_apply (.Apply (.UOp UserOp._at__at_mon) .__eo_List_nil) (.Rational (i : ℚ))))
          (.UOp UserOp._at__at_poly_zero)))
      (.Apply (.Apply (.UOp UserOp._at__at_poly) (.Apply (.Apply (.UOp UserOp._at__at_mon)
        (.Apply (.Apply .__eo_List_cons (.Numeral i)) .__eo_List_nil)) (.Rational (native_mk_rational 1 1))))
        (.UOp UserOp._at__at_poly_zero)) := by
  rw [__get_arith_poly_norm] <;> simp [__eo_to_q, native_to_real, native_mk_rational]

theorem V_const_of {q : ℚ} {t : Term}
    (e : __get_arith_poly_norm t =
      __eo_ite (__eo_is_q (.Rational q))
        (__eo_ite (__eo_is_eq (.Rational q) (.Rational (native_mk_rational 0 1))) (.UOp UserOp._at__at_poly_zero)
          (__eo_mk_apply (__eo_mk_apply (.UOp UserOp._at__at_poly)
            (__eo_mk_apply (.Apply (.UOp UserOp._at__at_mon) .__eo_List_nil) (.Rational q)))
            (.UOp UserOp._at__at_poly_zero))) t') : V t = C q := by
  unfold V; rw [e]
  rw [show __eo_is_q (.Rational q) = .Boolean true by simp [__eo_is_q, __eo_is_q_internal, native_and,
    native_not, native_teq], ite_true]
  by_cases hq : q = 0
  · subst hq
    rw [show __eo_is_eq (.Rational 0) (.Rational (native_mk_rational 0 1)) = .Boolean true by
      simp [__eo_is_eq, native_and, native_not, native_teq, rat_zero_eq], ite_true]
    simp
  · rw [show __eo_is_eq (.Rational q) (.Rational (native_mk_rational 0 1)) = .Boolean false by
      simp [__eo_is_eq, native_and, native_not, native_teq, rat_zero_eq, Ne.symm hq], ite_false]
    rw [mk_apply_eq (f := .Apply (.UOp UserOp._at__at_mon) .__eo_List_nil) (x := .Rational q)
      (by simp) (by simp)]
    rw [mk_apply_eq (f := .UOp UserOp._at__at_poly) (by simp) (by simp)]
    rw [mk_apply_eq (by simp) (by simp)]
    simp [coeffOf]

theorem V_rational (q : ℚ) : V (.Rational q) = C q := V_const_of (gn_rational q)

theorem V_numeral (i : Int) : V (.Numeral i) = C (i : ℚ) := V_const_of (gn_numeral i)

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith

/-! ## Translations of the operators telos decomposes -/

theorem toEo_sub (a b : Node) : (Node.app (.kind .SUB) ⟨[a, b]⟩).toEo =
    .Apply (.Apply (.UOp .neg) a.toEo) b.toEo := by
  simp [Node.toEo_app, Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]

theorem toEo_neg (a : Node) : (Node.app (.kind .NEG) ⟨[a]⟩).toEo = .Apply (.UOp .__eoo_neg_2) a.toEo := by
  simp [Node.toEo_app, Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]

theorem toEo_to_real (a : Node) : (Node.app (.kind .TO_REAL) ⟨[a]⟩).toEo = .Apply (.UOp .to_real) a.toEo := by
  simp [Node.toEo_app, Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]

theorem toEo_div (a b : Node) : (Node.app (.kind .DIVISION) ⟨[a, b]⟩).toEo =
    .Apply (.Apply (.UOp .qdiv) a.toEo) b.toEo := by
  simp [Node.toEo_app, Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]

theorem toEo_add (cs : Array Node) : (Node.app (.kind .ADD) cs).toEo =
    if 2 ≤ cs.size then eoRightAssocNil .plus (typedNil .plus ((cs.toList.map Node.toEo).headD .Stuck))
      (cs.toList.map Node.toEo) else .Stuck := by
  simp [Node.toEo_app, Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval]

theorem toEo_mult (cs : Array Node) : (Node.app (.kind .MULT) cs).toEo =
    if 2 ≤ cs.size then eoRightAssocNil .mult (typedNil .mult ((cs.toList.map Node.toEo).headD .Stuck))
      (cs.toList.map Node.toEo) else .Stuck := by
  simp [Node.toEo_app, Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval]

theorem NS_stuck : ¬ NS .Stuck := by simp [NS, __get_arith_poly_norm]

theorem V_typedNil_plus (x : Term) (h : NS (typedNil .plus x)) : V (typedNil .plus x) = 0 := by
  unfold typedNil at *
  generalize __eo_typeof x = T at *
  by_cases hT : T = .Stuck
  · subst hT; exact absurd h (by simpa [__eo_nil] using NS_stuck)
  · have e : __eo_nil (.UOp .plus) T = __arith_mk_zero T := by
      cases T <;> simp_all [__eo_nil, __eo_nil_plus]
    rw [e] at h ⊢
    have hc : __arith_mk_zero T = .Numeral 0 ∨ __arith_mk_zero T = .Rational (native_mk_rational 0 1) ∨
        __arith_mk_zero T = .Stuck := by unfold __arith_mk_zero; split <;> simp
    rcases hc with e | e | e <;> rw [e] at h ⊢
    · rw [V_numeral]; simp
    · rw [V_rational, rat_zero_eq]; simp
    · exact absurd h NS_stuck

theorem V_typedNil_mult (x : Term) (h : NS (typedNil .mult x)) : V (typedNil .mult x) = 1 := by
  unfold typedNil at *
  generalize __eo_typeof x = T at *
  by_cases hT : T = .Stuck
  · subst hT; exact absurd h (by simpa [__eo_nil] using NS_stuck)
  · have e : __eo_nil (.UOp .mult) T = __arith_mk_one T := by
      cases T <;> simp_all [__eo_nil, __eo_nil_mult]
    rw [e] at h ⊢
    have hc : __arith_mk_one T = .Numeral 1 ∨ __arith_mk_one T = .Rational (native_mk_rational 1 1) ∨
        __arith_mk_one T = .Stuck := by unfold __arith_mk_one; split <;> simp
    rcases hc with e | e | e <;> rw [e] at h ⊢
    · rw [V_numeral]; simp
    · rw [V_rational]; simp [native_mk_rational]
    · exact absurd h NS_stuck

theorem V_chain_plus {nil : Term} (hnil : NS nil → V nil = 0) :
    ∀ xs : List Term, NS (eoRightAssocNil .plus nil xs) →
      (∀ x ∈ xs, NS x) ∧ V (eoRightAssocNil .plus nil xs) = (xs.map V).sum
  | [], h => ⟨by simp, by rw [eoRightAssocNil] at h ⊢; simpa using hnil h⟩
  | x :: xs, h => by
    obtain ⟨h1, h2, e⟩ := V_plus (a := x) (b := eoRightAssocNil .plus nil xs) h
    obtain ⟨h3, e'⟩ := V_chain_plus hnil xs h2
    refine ⟨?_, ?_⟩
    · intro y hy; rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · exact h3 y hy
    · show V (eoApp2 .plus x _) = _
      rw [eoApp2, e, e']; simp

theorem V_chain_mult {nil : Term} (hnil : NS nil → V nil = 1) :
    ∀ xs : List Term, NS (eoRightAssocNil .mult nil xs) →
      (∀ x ∈ xs, NS x) ∧ V (eoRightAssocNil .mult nil xs) = (xs.map V).prod
  | [], h => ⟨by simp, by rw [eoRightAssocNil] at h ⊢; simpa using hnil h⟩
  | x :: xs, h => by
    obtain ⟨h1, h2, e⟩ := V_mult (a := x) (b := eoRightAssocNil .mult nil xs) h
    obtain ⟨h3, e'⟩ := V_chain_mult hnil xs h2
    refine ⟨?_, ?_⟩
    · intro y hy; rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · exact h3 y hy
    · show V (eoApp2 .mult x _) = _
      rw [eoApp2, e, e']; simp

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith

/-! ## telos's polynomials and their values -/

noncomputable def monoV (m : Mono) : P := (m.map fun l => V l.toEo).prod

/-- The value of a telos polynomial: its leaves are read by `V`, the value of their
translations' normal forms. -/
noncomputable def embedT (p : Poly) : P := (p.map fun e => C e.2 * monoV e.1).sum

/-- No monomial occurs twice. -/
def Keys (p : Poly) : Prop := (p.map Prod.fst).Nodup

@[simp] theorem embedT_nil : embedT [] = 0 := rfl
@[simp] theorem embedT_cons (e : Mono × Rat) (p : Poly) : embedT (e :: p) = C e.2 * monoV e.1 + embedT p := by
  simp [embedT]
@[simp] theorem embedT_append (p q : Poly) : embedT (p ++ q) = embedT p + embedT q := by
  simp [embedT]

theorem filter_of_not_mem {m : Mono} : ∀ {p : Poly}, m ∉ p.map Prod.fst →
    p.filter (fun e => !decide (e.1 = m)) = p
  | [], _ => rfl
  | e :: p, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [List.filter_cons, Ne.symm h.1, filter_of_not_mem h.2]

theorem embedT_find {m : Mono} : ∀ {p : Poly} {m' : Mono} {d : Rat}, Keys p →
    p.find? (fun e => decide (e.1 = m)) = some (m', d) →
    embedT p = embedT (p.filter (fun e => !decide (e.1 = m))) + C d * monoV m
  | [], _, _, _, h => by simp at h
  | e :: p, m', d, hk, h => by
    have hk' : e.1 ∉ p.map Prod.fst ∧ Keys p := by
      simpa [Keys, List.nodup_cons] using hk
    by_cases he : e.1 = m
    · simp only [List.find?_cons, he, decide_true, Option.some.injEq] at h
      subst h; subst he
      simp [List.filter_cons, filter_of_not_mem hk'.1]; ring
    · simp only [List.find?_cons, he, decide_false] at h
      rw [embedT_cons, embedT_find hk'.2 h]
      simp [List.filter_cons, he]; ring

theorem not_mem_of_find_none {m : Mono} {p : Poly} (h : p.find? (fun e => decide (e.1 = m)) = none) :
    m ∉ p.map Prod.fst := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
  have := List.find?_eq_none.1 h e he
  simp at this

theorem keys_filter {m : Mono} {p : Poly} (h : Keys p) :
    Keys (p.filter (fun e => !decide (e.1 = m))) ∧ m ∉ (p.filter (fun e => !decide (e.1 = m))).map Prod.fst := by
  refine ⟨?_, ?_⟩
  · exact (List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h)
  · intro hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    simp at he

theorem addMono_val (p : Poly) (m : Mono) (c : Rat) (hk : Keys p) :
    Keys (p.addMono m c) ∧ embedT (p.addMono m c) = embedT p + C c * monoV m := by
  unfold Poly.addMono
  by_cases hc : c = 0
  · simp [hc, hk]
  · simp only [hc, ↓reduceIte]
    split
    · next m' d hf =>
      obtain ⟨hk1, hm⟩ := keys_filter (m := m) hk
      have e := embedT_find hk hf
      by_cases hz : c + d = 0
      · simp only [hz, ↓reduceIte]
        refine ⟨hk1, ?_⟩
        rw [e, show c = -d by linear_combination hz]; simp
      · simp only [hz, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · simp only [Keys, List.map_append, List.map_cons, List.map_nil]
          exact List.nodup_append.2 ⟨hk1, List.nodup_singleton _, fun a ha b hb => by
            rw [List.mem_singleton] at hb; subst hb; rintro rfl; exact hm ha⟩
        · rw [e]; simp; ring
    · next hf =>
      have hm := not_mem_of_find_none hf
      refine ⟨?_, by simp⟩
      simp only [Keys, List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.2 ⟨hk, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton] at hb; subst hb; rintro rfl; exact hm ha⟩

theorem add_val : ∀ (q p : Poly), Keys p → Keys (p.add q) ∧ embedT (p.add q) = embedT p + embedT q
  | [], p, hk => ⟨hk, by simp [Poly.add]⟩
  | e :: q, p, hk => by
    have h1 := addMono_val p e.1 e.2 hk
    have h2 := add_val q (p.addMono e.1 e.2) h1.1
    simp only [Poly.add, List.foldl_cons] at h2 ⊢
    exact ⟨h2.1, by rw [h2.2, h1.2]; simp; ring⟩

theorem scale_val (p : Poly) (c : Rat) (hk : Keys p) :
    Keys (p.scale c) ∧ embedT (p.scale c) = C c * embedT p := by
  unfold Poly.scale
  by_cases hc : c = 0
  · simp [hc, Keys]
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · have e : (p.map fun x : Mono × Rat => (x.1, c * x.2)).map Prod.fst = p.map Prod.fst := by
        simp [List.map_map, Function.comp_def]
      unfold Keys; rw [e]; exact hk
    simp only [embedT, List.map_map]
    rw [← List.sum_map_mul_left]
    congr 1; apply List.map_congr_left; intro e _; simp; ring

theorem sortLeaves_insert_perm (x : Node) : ∀ l : List Node, List.Perm (sortLeaves.insert x l) (x :: l)
  | [] => by simp [sortLeaves.insert]
  | y :: ys => by
    unfold sortLeaves.insert
    split
    · exact ((sortLeaves_insert_perm x ys).cons y).trans (List.Perm.swap x y ys)
    · exact List.Perm.refl _

theorem sortLeaves_perm : ∀ l : List Node, List.Perm (sortLeaves l) l
  | [] => by simp [sortLeaves]
  | x :: xs => by
    have h := sortLeaves_perm xs
    simp only [sortLeaves, List.foldr_cons] at h ⊢
    exact (sortLeaves_insert_perm x _).trans (h.cons x)

theorem monoV_perm {l l' : List Node} (h : List.Perm l l') : monoV l = monoV l' := by
  unfold monoV; exact (h.map _).prod_eq

theorem monoV_append (l l' : List Node) : monoV (l ++ l') = monoV l * monoV l' := by
  simp [monoV]

theorem mul_inner_val (m₁ : Mono) (c₁ : Rat) : ∀ (q acc : Poly), Keys acc →
    Keys (q.foldl (fun acc (e : Mono × Rat) => acc.addMono (sortLeaves (m₁ ++ e.1)) (c₁ * e.2)) acc) ∧
    embedT (q.foldl (fun acc (e : Mono × Rat) => acc.addMono (sortLeaves (m₁ ++ e.1)) (c₁ * e.2)) acc) =
      embedT acc + C c₁ * monoV m₁ * embedT q
  | [], acc, hk => ⟨hk, by simp⟩
  | e :: q, acc, hk => by
    have h1 := addMono_val acc (sortLeaves (m₁ ++ e.1)) (c₁ * e.2) hk
    have h2 := mul_inner_val m₁ c₁ q _ h1.1
    simp only [List.foldl_cons]
    refine ⟨h2.1, ?_⟩
    rw [h2.2, h1.2, monoV_perm (sortLeaves_perm _), monoV_append]; simp; ring

theorem mul_val (p q : Poly) : Keys (p.mul q) ∧ embedT (p.mul q) = embedT p * embedT q := by
  unfold Poly.mul
  suffices h : ∀ (p acc : Poly), Keys acc →
      Keys (p.foldl (fun acc (e : Mono × Rat) =>
        q.foldl (fun acc (f : Mono × Rat) => acc.addMono (sortLeaves (e.1 ++ f.1)) (e.2 * f.2)) acc) acc) ∧
      embedT (p.foldl (fun acc (e : Mono × Rat) =>
        q.foldl (fun acc (f : Mono × Rat) => acc.addMono (sortLeaves (e.1 ++ f.1)) (e.2 * f.2)) acc) acc) =
        embedT acc + embedT p * embedT q by
    have := h p [] (by simp [Keys]); simpa using this
  intro p
  induction p with
  | nil => intro acc hk; exact ⟨hk, by simp⟩
  | cons e p ih =>
    intro acc hk
    have h1 := mul_inner_val e.1 e.2 q acc hk
    have h2 := ih _ h1.1
    simp only [List.foldl_cons]
    refine ⟨h2.1, ?_⟩
    rw [h2.2, h1.2]; simp; ring

theorem const_val (c : Rat) : Keys (Poly.const c) ∧ embedT (Poly.const c) = C c := by
  have := addMono_val [] [] c (by simp [Keys])
  simpa [Poly.const, monoV] using this

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith

theorem foldl_add_val : ∀ (ps : List Poly) (acc : Poly), Keys acc →
    Keys (ps.foldl Poly.add acc) ∧ embedT (ps.foldl Poly.add acc) = embedT acc + (ps.map embedT).sum
  | [], acc, hk => ⟨hk, by simp⟩
  | p :: ps, acc, hk => by
    have h1 := add_val p acc hk
    have h2 := foldl_add_val ps _ h1.1
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    exact ⟨h2.1, by rw [h2.2, h1.2]; ring⟩

theorem foldl_mul_val : ∀ (ps : List Poly) (acc : Poly), Keys acc →
    Keys (ps.foldl Poly.mul acc) ∧ embedT (ps.foldl Poly.mul acc) = embedT acc * (ps.map embedT).prod
  | [], acc, hk => ⟨hk, by simp⟩
  | p :: ps, acc, _ => by
    have h1 := mul_val acc p
    have h2 := foldl_mul_val ps _ h1.1
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    exact ⟨h2.1, by rw [h2.2, h1.2]; ring⟩

theorem attach_map_polyOf (cs : Array Node) :
    (cs.attach.toList.map fun x => match x with | ⟨c, _⟩ => polyOf c) = cs.toList.map polyOf := by
  simp

theorem single_val (n : Node) : Keys [([n], (1 : Rat))] ∧ V n.toEo = embedT [([n], 1)] := by
  simp [Keys, monoV]

/-- The value of a list of children, given the value of each. -/
theorem sum_children {cs : Array Node}
    (ih : ∀ c ∈ cs, NS c.toEo → Keys (polyOf c) ∧ V c.toEo = embedT (polyOf c))
    (hns : ∀ x ∈ cs.toList.map Node.toEo, NS x) :
    ((cs.toList.map Node.toEo).map V) = (cs.toList.map polyOf).map embedT := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact (ih c (Array.mem_def.2 hc) (hns _ (List.mem_map_of_mem hc))).2

theorem toEo_int (i : Int) : (Node.const (.integer i)).toEo = .Numeral i := by
  rw [Node.toEo]; rfl
theorem toEo_rat (q : Rat) : (Node.const (.rational q)).toEo = .Rational q := by
  rw [Node.toEo]; rfl

theorem polyOf_val : ∀ n : Node, NS n.toEo → Keys (polyOf n) ∧ V n.toEo = embedT (polyOf n) := by
  intro n h
  fun_induction polyOf n with
  | case1 i => exact ⟨(const_val _).1, by rw [(const_val _).2]; rw [toEo_int]; exact V_numeral i⟩
  | case2 q => exact ⟨(const_val _).1, by rw [(const_val _).2]; rw [toEo_rat]; exact V_rational q⟩
  | case3 cs ih =>
    rw [attach_map_polyOf]
    rw [toEo_add] at h ⊢
    by_cases hs : 2 ≤ cs.size
    · simp only [hs, ↓reduceIte] at h ⊢
      obtain ⟨hns, e⟩ := V_chain_plus (fun h' => V_typedNil_plus _ h') _ h
      have hf := foldl_add_val (cs.toList.map polyOf) [] (by simp [Keys])
      refine ⟨hf.1, ?_⟩
      rw [e, hf.2, sum_children ih hns]; simp
    · simp only [hs, ↓reduceIte] at h; exact absurd h NS_stuck
  | case4 a b iha ihb =>
    rw [toEo_sub] at h ⊢
    obtain ⟨h1, h2, e⟩ := V_sub h
    obtain ⟨ka, va⟩ := iha h1
    obtain ⟨kb, vb⟩ := ihb h2
    have hs := scale_val (polyOf b) (-1) kb
    have ha := add_val ((polyOf b).scale (-1)) (polyOf a) ka
    refine ⟨ha.1, ?_⟩
    rw [e, ha.2, hs.2, va, vb]; simp; ring
  | case5 a ih =>
    rw [toEo_neg] at h ⊢
    obtain ⟨h1, e⟩ := V_uneg h
    obtain ⟨ka, va⟩ := ih h1
    have hs := scale_val (polyOf a) (-1) ka
    refine ⟨hs.1, ?_⟩
    rw [e, hs.2, va]; simp
  | case6 cs ih =>
    rw [attach_map_polyOf]
    rw [toEo_mult] at h ⊢
    by_cases hs : 2 ≤ cs.size
    · simp only [hs, ↓reduceIte] at h ⊢
      obtain ⟨hns, e⟩ := V_chain_mult (fun h' => V_typedNil_mult _ h') _ h
      have hf := foldl_mul_val (cs.toList.map polyOf) (Poly.const 1) (const_val 1).1
      refine ⟨hf.1, ?_⟩
      rw [e, hf.2, (const_val 1).2, sum_children ih hns]; simp
    · simp only [hs, ↓reduceIte] at h; exact absurd h NS_stuck
  | case7 a ih =>
    rw [toEo_to_real] at h ⊢
    obtain ⟨h1, e⟩ := V_to_real h
    obtain ⟨ka, va⟩ := ih h1
    exact ⟨ka, by rw [e, va]⟩
  | case8 a q => exact single_val _
  | case9 a q hq ih =>
    rw [toEo_div, toEo_rat] at h ⊢
    have hq' : q ≠ 0 := by simpa using hq
    obtain ⟨h1, e⟩ := V_qdiv_rat hq' h
    obtain ⟨ka, va⟩ := ih h1
    have hs := scale_val (polyOf a) (1 / q) ka
    exact ⟨hs.1, by rw [e, hs.2, va]⟩
  | case10 a i => exact single_val _
  | case11 a i hi ih =>
    rw [toEo_div, toEo_int] at h ⊢
    have hi' : i ≠ 0 := by simpa using hi
    obtain ⟨h1, e⟩ := V_qdiv_num hi' h
    obtain ⟨ka, va⟩ := ih h1
    have hs := scale_val (polyOf a) (1 / (i : Rat)) ka
    exact ⟨hs.1, by rw [e, hs.2, va]⟩
  | case12 n => exact single_val n

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith Telos.Node

/-! ## Rendering a polynomial keeps its value -/

theorem toEo_mkNode_to_real (a : Node) : (mkNode .TO_REAL #[a]).toEo = .Apply (.UOp .to_real) a.toEo :=
  toEo_to_real a

theorem V_wrap {real : Bool} {l : Node} (h : NS (wrapLeaf real l).toEo) :
    NS l.toEo ∧ V (wrapLeaf real l).toEo = V l.toEo := by
  unfold wrapLeaf at *
  split
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    rw [toEo_mkNode_to_real] at h ⊢; exact V_to_real h
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact ⟨h, rfl⟩

/-- The value of an application of `*` or `+` to at least two children. -/
theorem V_mult_list {xs : List Node} (hlen : 2 ≤ xs.length) (h : NS (mkNode .MULT xs.toArray).toEo) :
    (∀ x ∈ xs, NS x.toEo) ∧ V (mkNode .MULT xs.toArray).toEo = (xs.map fun x => V x.toEo).prod := by
  unfold mkNode at *
  rw [toEo_mult] at h ⊢
  simp only [List.size_toArray, hlen, ↓reduceIte, List.toList_toArray] at h ⊢
  obtain ⟨hns, e⟩ := V_chain_mult (fun h' => V_typedNil_mult _ h') _ h
  exact ⟨fun x hx => hns _ (List.mem_map_of_mem hx), by rw [e, List.map_map]; rfl⟩

theorem V_add_list {xs : List Node} (hlen : 2 ≤ xs.length) (h : NS (mkNode .ADD xs.toArray).toEo) :
    (∀ x ∈ xs, NS x.toEo) ∧ V (mkNode .ADD xs.toArray).toEo = (xs.map fun x => V x.toEo).sum := by
  unfold mkNode at *
  rw [toEo_add] at h ⊢
  simp only [List.size_toArray, hlen, ↓reduceIte, List.toList_toArray] at h ⊢
  obtain ⟨hns, e⟩ := V_chain_plus (fun h' => V_typedNil_plus _ h') _ h
  exact ⟨fun x hx => hns _ (List.mem_map_of_mem hx), by rw [e, List.map_map]; rfl⟩

theorem V_product {fs : List Node} (hne : fs ≠ []) (h : NS (productNode fs).toEo) :
    (∀ f ∈ fs, NS f.toEo) ∧ V (productNode fs).toEo = (fs.map fun f => V f.toEo).prod := by
  match fs, hne with
  | [x], _ => exact ⟨by simpa [productNode] using h, by simp [productNode]⟩
  | x :: y :: zs, _ => exact V_mult_list (by simp) h

theorem V_monoNode {real : Bool} {fs : Mono} (hne : fs ≠ []) (h : NS (monoNode real fs).toEo) :
    V (monoNode real fs).toEo = monoV fs := by
  unfold monoNode at *
  obtain ⟨hns, e⟩ := V_product (by simpa using hne) h
  rw [e, monoV, List.map_map]
  congr 1; apply List.map_congr_left
  intro f hf
  exact (V_wrap (hns _ (List.mem_map_of_mem hf))).2

theorem V_constNode {real : Bool} {c : Rat} (hc : real = true ∨ c.isInt = true) :
    V (constNode real c).toEo = C c := by
  unfold constNode
  split
  · rw [toEo_rat, V_rational]
  · rename_i hr
    have hi : c.den = 1 := by
      rcases hc with hc | hc
      · simp_all
      · simpa [Rat.isInt] using hc
    rw [toEo_int, V_numeral]
    congr 1; exact Rat.coe_int_num_of_den_eq_one hi

theorem V_two_mult {a b : Node} (h : NS (mkNode .MULT #[a, b]).toEo) :
    NS a.toEo ∧ NS b.toEo ∧ V (mkNode .MULT #[a, b]).toEo = V a.toEo * V b.toEo := by
  have := V_mult_list (xs := [a, b]) (by simp) h
  exact ⟨this.1 a (by simp), this.1 b (by simp), by rw [this.2]; simp⟩

theorem V_termNode {real : Bool} {fs : Mono} {c : Rat} (hc : real = true ∨ c.isInt = true)
    (h : NS (termNode real (fs, c)).toEo) : V (termNode real (fs, c)).toEo = C c * monoV fs := by
  cases fs with
  | nil => simp only [termNode] at h ⊢; rw [V_constNode hc]; simp [monoV]
  | cons f fs =>
    have hne : f :: fs ≠ [] := by simp
    simp only [termNode] at h ⊢
    by_cases hra : (real && (f :: fs).all isInt) = true
    · simp only [hra, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hci : c.isInt = true
      · simp only [hci, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [toEo_mkNode_to_real] at h ⊢
        obtain ⟨h1, e⟩ := V_to_real h
        rw [e]
        by_cases h1c : c = 1
        · simp only [h1c, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
          rw [(V_product hne h1).2, monoV]; simp
        · simp only [h1c, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
          obtain ⟨-, h3, e2⟩ := V_two_mult h1
          rw [e2, V_constNode (Or.inr hci), (V_product hne h3).2, monoV]
      · simp only [hci, Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨-, h3, e2⟩ := V_two_mult h
        rw [toEo_mkNode_to_real] at h3
        obtain ⟨h4, e3⟩ := V_to_real h3
        rw [e2, V_constNode (Or.inl rfl), toEo_mkNode_to_real, e3, (V_product hne h4).2, monoV]
    · simp only [hra, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases h1c : c = 1
      · simp only [h1c, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [V_monoNode hne h]; simp
      · simp only [h1c, Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨-, h3, e2⟩ := V_two_mult h
        rw [e2, V_constNode hc, V_monoNode hne h3]

theorem V_sumNode {real : Bool} {ts : List Node} (h : NS (sumNode real ts).toEo) :
    (∀ t ∈ ts, NS t.toEo) ∧ V (sumNode real ts).toEo = (ts.map fun t => V t.toEo).sum := by
  match ts with
  | [] => exact ⟨by simp, by simp [sumNode, V_constNode (c := 0) (Or.inr rfl)]⟩
  | [t] => exact ⟨by simpa [sumNode] using h, by simp [sumNode]⟩
  | t :: u :: us => exact V_add_list (by simp) h

theorem embedT_perm {p q : Poly} (h : List.Perm p q) : embedT p = embedT q := by
  unfold embedT; exact (h.map _).sum_eq

theorem V_toNodeAt {real : Bool} {p : Poly} (hc : real = true ∨ p.all (·.2.isInt) = true)
    (h : NS (p.toNodeAt real).toEo) : V (p.toNodeAt real).toEo = embedT p := by
  unfold Poly.toNodeAt at *
  obtain ⟨hns, e⟩ := V_sumNode h
  rw [e, ← embedT_perm (List.mergeSort_perm p _), embedT, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hmem : t ∈ p := (List.mergeSort_perm p _).mem_iff.1 ht
  have hc' : real = true ∨ t.2.isInt = true := by
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by simpa using List.all_eq_true.1 hc t hmem)
  exact V_termNode hc' (hns _ (List.mem_map_of_mem ht))

theorem V_toNode {real : Bool} {p : Poly} (hc : real = true ∨ p.all (·.2.isInt) = true)
    (h : NS (p.toNode real).toEo) : V (p.toNode real).toEo = embedT p := by
  unfold Poly.toNode at *
  split
  · rename_i hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    rw [toEo_mkNode_to_real] at h ⊢
    obtain ⟨h1, e⟩ := V_to_real h
    have hall : (p.all fun x => x.2.isInt) = true := by
      simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
    rw [e, V_toNodeAt (Or.inr hall) h1]
  · rename_i hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    exact V_toNodeAt hc h

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith Telos.Node

/-! ## telos's normal form has Logos's normal form -/

theorem smtty_eq (a b : Term) : smtty (.Apply (.Apply (.UOp .eq) a) b) = __smtx_typeof_eq (smtty a) (smtty b) := by
  unfold smtty
  rw [show __eo_to_smt (.Apply (.Apply (.UOp .eq) a) b) = SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) from rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

theorem eq_types {T U : SmtType} (h : __smtx_typeof_eq T U = .Bool) : T = U := by
  unfold __smtx_typeof_eq __smtx_typeof_guard at h
  cases T <;> simp_all [native_ite, native_Teq]
  all_goals (split at h <;> simp_all)

/-- **telos's arithmetic normal form is accepted by `arith_poly_norm`**: under
`ArithNormOk`, `n` and `arithNorm n` have the same Logos normal form, which is
not stuck. -/
theorem arithNorm_get_norm {n : Node} (h : ArithNormOk n (polyOf n) (arithNorm n)) :
    __get_arith_poly_norm n.toEo ≠ .Stuck ∧
      __get_arith_poly_norm n.toEo = __get_arith_poly_norm (arithNorm n).toEo := by
  obtain ⟨hty, heq, hint⟩ := h
  have hn : ArithTy (smtty n.toEo) := hty
  have hmn : smtty n.toEo = smtty (arithNorm n).toEo := by
    have : smtty (eqFormula n (arithNorm n)) = .Bool := heq
    rw [eqFormula, eoApp2, smtty_eq] at this
    exact eq_types this
  have hm : ArithTy (smtty (arithNorm n).toEo) := hmn ▸ hn
  have ns_n := get_norm_ne_stuck _ hn
  have ns_m := get_norm_ne_stuck _ hm
  refine ⟨ns_n, get_norm_eq_of_polyVal_eq ns_n ns_m ?_⟩
  show V n.toEo = V (arithNorm n).toEo
  rw [(polyOf_val n ns_n).2]
  exact (V_toNode hint ns_m).symm

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith Telos.Node

/-- **The static step is a CPC step**: under `ArithNormOk`, Logos's checker,
run on `[arith_poly_norm (= n (arithNorm n))]` from the empty state, proves
`(= n (arithNorm n))`. The Eunoia type of the equation is assumed here
(`hty`) and derived from its SMT type in `ArithNorm.lean`. -/
theorem arithNorm_provesEq_of_typeof {n : Node} (h : ArithNormOk n (polyOf n) (arithNorm n))
    (hty : __eo_typeof (eqFormula n (arithNorm n)) = .Bool) :
    ProvesEq (Certified.arithNormCmds n) n (arithNorm n) := by
  obtain ⟨hns, hgn⟩ := arithNorm_get_norm h
  have hF : __eo_prog_arith_poly_norm (eqFormula n (arithNorm n)) = eqFormula n (arithNorm n) := by
    simp only [eqFormula, eoApp2, __eo_prog_arith_poly_norm, __eo_requires, native_ite, native_teq,
      native_not, hgn]
    simp [← hgn, hns]
  have hbool : __eo_is_bool_type (eqFormula n (arithNorm n)) = .Boolean true := by
    have hne : eqFormula n (arithNorm n) ≠ .Stuck := by simp [eqFormula, eoApp2]
    unfold __eo_is_bool_type
    split
    · next he => exact absurd he hne
    · rw [hty]; simp [__eo_eq, native_teq]
  have hrun : runFromEmpty (Certified.arithNormCmds n) =
      CState.cons (CStateObj.proven (eqFormula n (arithNorm n))) CState.nil := by
    show __eo_invoke_cmd_list CState.nil
      (.cons (.step .arith_poly_norm (.cons (eqFormula n (arithNorm n)) .nil) .nil) .nil) = _
    rw [__eo_invoke_cmd_list, __eo_invoke_cmd_list, __eo_invoke_cmd] <;> try simp
    rw [show __eo_cmd_step_proven CState.nil CRule.arith_poly_norm (.cons (eqFormula n (arithNorm n)) .nil) .nil =
      __eo_prog_arith_poly_norm (eqFormula n (arithNorm n)) from rfl, hF]
    rw [__eo_push_proven, hbool, __eo_push_proven_check]
  refine ⟨?_, ?_, ?_⟩
  · refine CmdListTranslationOk.cons _ _ ?_ CmdListTranslationOk.nil
    show cArgListTranslationOk (.cons (eqFormula n (arithNorm n)) .nil)
    refine ⟨?_, trivial⟩
    show __smtx_typeof (__eo_to_smt (eqFormula n (arithNorm n))) ≠ .None
    rw [h.2.1]; simp
  · rw [hrun]; rfl
  · rw [hrun]; rfl

end Telos.PolyNorm

namespace Telos.PolyNorm
open Telos.TermOrder Smtm Telos.Arith Telos.Node

/-! ## Equations between terms with the same telos polynomial -/

/-- If `a` and `b` have the same telos polynomial up to order (and `(= a b)` is
well typed, `a` arithmetic), they have the same Logos normal form, not stuck. -/
theorem polyEq_get_norm {a b : Node} (hty : a.smtType = .Int ∨ a.smtType = .Real)
    (heq : __smtx_typeof (__eo_to_smt (eqFormula a b)) = .Bool) (hp : List.Perm (polyOf a) (polyOf b)) :
    __get_arith_poly_norm a.toEo ≠ .Stuck ∧ __get_arith_poly_norm a.toEo = __get_arith_poly_norm b.toEo := by
  have ha : ArithTy (smtty a.toEo) := hty
  have hab : smtty a.toEo = smtty b.toEo := by
    have : smtty (eqFormula a b) = .Bool := heq
    rw [eqFormula, eoApp2, smtty_eq] at this
    exact eq_types this
  have hb : ArithTy (smtty b.toEo) := hab ▸ ha
  have ns_a := get_norm_ne_stuck _ ha
  have ns_b := get_norm_ne_stuck _ hb
  refine ⟨ns_a, get_norm_eq_of_polyVal_eq ns_a ns_b ?_⟩
  show V a.toEo = V b.toEo
  rw [(polyOf_val a ns_a).2, (polyOf_val b ns_b).2, embedT_perm hp]

theorem eqFormula_ne_stuck (a b : Node) : eqFormula a b ≠ .Stuck := by simp [eqFormula, eoApp2]

theorem is_bool_type_of_typeof {F : Term} (hne : F ≠ .Stuck) (hty : __eo_typeof F = .Bool) :
    __eo_is_bool_type F = .Boolean true := by
  have e : __eo_is_bool_type F = __eo_eq (__eo_typeof F) .Bool := by
    cases F <;> first | rfl | exact absurd rfl hne
  rw [e, hty]; simp [__eo_eq, native_teq]

theorem prog_poly_norm_eq {a b : Node}
    (h : __get_arith_poly_norm a.toEo ≠ .Stuck ∧ __get_arith_poly_norm a.toEo = __get_arith_poly_norm b.toEo) :
    __eo_prog_arith_poly_norm (eqFormula a b) = eqFormula a b := by
  obtain ⟨hns, hgn⟩ := h
  simp only [eqFormula, eoApp2, __eo_prog_arith_poly_norm, __eo_requires, native_ite, native_teq,
    native_not, hgn]
  simp [← hgn, hns]

/-- **The static `arith_poly_norm_rel` steps are CPC steps**, given the Eunoia
types of the two equations (derived from their SMT types in `ArithNorm.lean`). -/
theorem arithRel_provesEq_of_typeof {n m a b : Node} (h : ArithRelOk n m a b)
    (htyP : __eo_typeof (eqFormula a b) = .Bool) (htyF : __eo_typeof (eqFormula n m) = .Bool) :
    ProvesEq (Certified.arithRelCmds n m a b) n m := by
  obtain ⟨hty, heq, hp, hF, hrel⟩ := h
  have hP := prog_poly_norm_eq (polyEq_get_norm hty heq hp)
  have hbP := is_bool_type_of_typeof (eqFormula_ne_stuck a b) htyP
  have hbF := is_bool_type_of_typeof (eqFormula_ne_stuck n m) htyF
  have hrun : runFromEmpty (Certified.arithRelCmds n m a b) =
      CState.cons (CStateObj.proven (eqFormula n m))
        (CState.cons (CStateObj.proven (eqFormula a b)) CState.nil) := by
    show __eo_invoke_cmd_list CState.nil
      (.cons (.step .arith_poly_norm (.cons (eqFormula a b) .nil) .nil)
        (.cons (.step .arith_poly_norm_rel (.cons (eqFormula n m) .nil) (.cons 0 .nil)) .nil)) = _
    rw [__eo_invoke_cmd_list, __eo_invoke_cmd] <;> try simp
    rw [show __eo_cmd_step_proven CState.nil CRule.arith_poly_norm (.cons (eqFormula a b) .nil) .nil =
      __eo_prog_arith_poly_norm (eqFormula a b) from rfl, hP, __eo_push_proven, hbP, __eo_push_proven_check]
    rw [__eo_invoke_cmd_list, __eo_invoke_cmd_list, __eo_invoke_cmd] <;> try simp
    rw [show __eo_cmd_step_proven (CState.cons (CStateObj.proven (eqFormula a b)) CState.nil)
        CRule.arith_poly_norm_rel (.cons (eqFormula n m) .nil) (.cons 0 .nil) =
      __eo_prog_arith_poly_norm_rel (eqFormula n m) (Proof.pf (eqFormula a b)) from rfl, hrel,
      __eo_push_proven, hbF, __eo_push_proven_check]
  refine ⟨?_, ?_, ?_⟩
  · refine CmdListTranslationOk.cons _ _ ?_ (CmdListTranslationOk.cons _ _ ?_ CmdListTranslationOk.nil)
    · show cArgListTranslationOk (.cons (eqFormula a b) .nil)
      refine ⟨?_, trivial⟩
      show __smtx_typeof (__eo_to_smt (eqFormula a b)) ≠ .None
      rw [heq]; simp
    · show cArgListTranslationOk (.cons (eqFormula n m) .nil)
      refine ⟨?_, trivial⟩
      show __smtx_typeof (__eo_to_smt (eqFormula n m)) ≠ .None
      rw [hF]; simp
  · rw [hrun]; rfl
  · rw [hrun]; rfl

end Telos.PolyNorm
