import TelosProofs.Core.CondEquiv

/-!
# Congruence of `distinct`, under a condition

`(distinct x₁ … xₙ)` is written in CPC as `distinct` applied to a typed list
`(@@TypedList_cons x₁ … (@@TypedList_cons xₙ nil))` (`AppShape.typedList`), and
Logos translates it as the conjunction of the pairwise disequalities of the
translated elements (`__eo_to_smt_distinct`), when the elements have one type
(`__eo_to_smt_typed_list_elem_type`). So:

* the elements of a well-typed `distinct` are well typed (`distinct_children`);
* elements related under a condition give `distinct`s related under it
  (`condEquiv_distinct`): the types of the two translations are built from the
  same element types, and their values from the values of equalities between
  related values, which are the same (`eval_eq_congr`).

Everything here is proved from Logos's definitions and the facts about
`SmtValueRel` (`LogosFacts`).
-/

open Eo Smtm SmtEval

namespace Telos

set_option linter.unusedSectionVars false
set_option linter.internalConstructors false

/-- A typed list with the given nil. -/
abbrev TL (nil : Term) (xs : List Term) : Term :=
  eoRightAssocNil UserOp._at__at_TypedList_cons nil xs

/-- The elements of a typed list with an element type are well typed. -/
theorem tl_elems_typed (nil : Term) : ∀ xs : List Term,
    __eo_to_smt_typed_list_elem_type (TL nil xs) ≠ SmtType.None → ∀ x ∈ xs, HasSmtType x
  | [], _ => by simp
  | x :: xs, h => by
    simp only [TL, eoRightAssocNil, eoApp2, __eo_to_smt_typed_list_elem_type, native_ite,
      native_Teq] at h
    by_cases he : __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_typed_list_elem_type (eoRightAssocNil UserOp._at__at_TypedList_cons nil xs)
    · simp only [he, decide_true, ite_true] at h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · unfold HasSmtType; rw [he]; exact h
      · exact tl_elems_typed nil xs h y hy
    · simp [he] at h

theorem typeof_none : __smtx_typeof SmtTerm.None = SmtType.None := by
  rw [__smtx_typeof.eq_def]

/-- **The elements of a well-typed `distinct` are well typed.** -/
theorem distinct_children (xs : List Term)
    (h : HasSmtType ((AppShape.typedList UserOp.distinct).toEo xs)) : ∀ x ∈ xs, HasSmtType x := by
  simp only [AppShape.toEo] at h
  split at h
  · simp only [eoApp1, HasSmtType, __eo_to_smt, native_ite, native_Teq] at h
    by_cases he : __eo_to_smt_typed_list_elem_type (eoRightAssocNil UserOp._at__at_TypedList_cons
        (typedNil UserOp._at__at_TypedList_cons (xs.headD Term.Stuck)) xs) = SmtType.None
    · simp only [he, decide_true, ite_true] at h; exact absurd typeof_none h
    · exact tl_elems_typed _ xs he
  · exact absurd typeof_none (by simpa [HasSmtType, __eo_to_smt] using h)

/-! ## Types -/

/-- The nil of a typed list: stuck, or `(@@TypedList_nil T)`. -/
theorem typedNil_shape (x : Term) :
    typedNil UserOp._at__at_TypedList_cons x = Term.Stuck ∨
      ∃ T, typedNil UserOp._at__at_TypedList_cons x =
        Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T := by
  unfold typedNil
  simp only [typedNilOfType]
  split
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

/-- Element-wise relations of the lists of two typed lists. -/
abbrev SameTypes (xs ys : List Term) : Prop :=
  List.Forall₂ (fun x y => __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y)) xs ys

theorem elem_type_congr (nil : Term) {xs ys : List Term} (h : SameTypes xs ys) :
    __eo_to_smt_typed_list_elem_type (TL nil xs) = __eo_to_smt_typed_list_elem_type (TL nil ys) := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    simp only [TL, eoRightAssocNil, eoApp2, __eo_to_smt_typed_list_elem_type] at ih ⊢
    rw [hxy, ih]

theorem pairs_nil_eq (x : Term) (s s' : SmtTerm) :
    __eo_to_smt_distinct_pairs s (typedNil UserOp._at__at_TypedList_cons x) =
      __eo_to_smt_distinct_pairs s' (typedNil UserOp._at__at_TypedList_cons x) := by
  rcases typedNil_shape x with h | ⟨T, h⟩ <;> rw [h] <;> simp [__eo_to_smt_distinct_pairs]

theorem typeof_pairs_congr (x : Term) {s s' : SmtTerm} (hs : __smtx_typeof s = __smtx_typeof s')
    {xs ys : List Term} (h : SameTypes xs ys) :
    __smtx_typeof (__eo_to_smt_distinct_pairs s (TL (typedNil UserOp._at__at_TypedList_cons x) xs)) =
      __smtx_typeof (__eo_to_smt_distinct_pairs s' (TL (typedNil UserOp._at__at_TypedList_cons x) ys)) := by
  induction h with
  | nil => simp only [TL, eoRightAssocNil]; rw [pairs_nil_eq x s s']
  | cons hxy _ ih =>
    simp only [TL, eoRightAssocNil, eoApp2, __eo_to_smt_distinct_pairs] at ih ⊢
    simp only [__smtx_typeof, hs, hxy, ih]

theorem typeof_distinct_congr (x : Term) {xs ys : List Term} (h : SameTypes xs ys) :
    __smtx_typeof (__eo_to_smt_distinct (TL (typedNil UserOp._at__at_TypedList_cons x) xs)) =
      __smtx_typeof (__eo_to_smt_distinct (TL (typedNil UserOp._at__at_TypedList_cons x) ys)) := by
  induction h with
  | nil => rfl
  | @cons a b _ _ hxy hr ih =>
    simp only [TL, eoRightAssocNil, eoApp2, __eo_to_smt_distinct] at ih ⊢
    simp only [__smtx_typeof, ih, typeof_pairs_congr x hxy hr]

/-! ## Values -/

theorem eval_eq_bool (a b : SmtValue) : ∃ c, __smtx_model_eval_eq a b = SmtValue.Boolean c := by
  unfold __smtx_model_eval_eq; split <;> exact ⟨_, rfl⟩

variable [LogosFacts]

/-- Equality of related values is the same. -/
theorem eval_eq_congr {a a' b b' : SmtValue} (ha : SmtValueRel a a') (hb : SmtValueRel b b') :
    __smtx_model_eval_eq a b = __smtx_model_eval_eq a' b' := by
  obtain ⟨c, hc⟩ := eval_eq_bool a b
  obtain ⟨c', hc'⟩ := eval_eq_bool a' b'
  have hiff : SmtValueRel a b ↔ SmtValueRel a' b' :=
    ⟨fun h => LogosFacts.value_rel_trans _ _ _
        (LogosFacts.value_rel_trans _ _ _ (LogosFacts.value_rel_symm _ _ ha) h) hb,
     fun h => LogosFacts.value_rel_trans _ _ _ (LogosFacts.value_rel_trans _ _ _ ha h)
        (LogosFacts.value_rel_symm _ _ hb)⟩
  unfold SmtValueRel at hiff
  rw [hc, hc'] at hiff ⊢
  cases c <;> cases c' <;> simp_all

/-- Element-wise related values in `M`. -/
abbrev RelVals (M : SmtModel) (xs ys : List Term) : Prop :=
  List.Forall₂ (fun x y => SmtValueRel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y))) xs ys

theorem eval_pairs_congr (M : SmtModel) (x : Term) {s s' : SmtTerm}
    (hs : SmtValueRel (__smtx_model_eval M s) (__smtx_model_eval M s'))
    {xs ys : List Term} (h : RelVals M xs ys) :
    __smtx_model_eval M (__eo_to_smt_distinct_pairs s (TL (typedNil UserOp._at__at_TypedList_cons x) xs)) =
      __smtx_model_eval M (__eo_to_smt_distinct_pairs s' (TL (typedNil UserOp._at__at_TypedList_cons x) ys)) := by
  induction h with
  | nil => simp only [TL, eoRightAssocNil]; rw [pairs_nil_eq x s s']
  | cons hxy _ ih =>
    simp only [TL, eoRightAssocNil, eoApp2, __eo_to_smt_distinct_pairs] at ih ⊢
    simp only [__smtx_model_eval, ih, eval_eq_congr hs hxy]

theorem eval_distinct_congr (M : SmtModel) (x : Term) {xs ys : List Term} (h : RelVals M xs ys) :
    __smtx_model_eval M (__eo_to_smt_distinct (TL (typedNil UserOp._at__at_TypedList_cons x) xs)) =
      __smtx_model_eval M (__eo_to_smt_distinct (TL (typedNil UserOp._at__at_TypedList_cons x) ys)) := by
  induction h with
  | nil => rfl
  | @cons a b _ _ hxy hr ih =>
    simp only [TL, eoRightAssocNil, eoApp2, __eo_to_smt_distinct] at ih ⊢
    simp only [__smtx_model_eval, ih, eval_pairs_congr M x hxy hr]

/-- **Congruence of `distinct`** under a condition. -/
theorem condEquiv_distinct {Φ : SmtModel → Prop} {xs ys : List Term}
    (h : List.Forall₂ (CondEquiv Φ) xs ys)
    (ht : HasSmtType ((AppShape.typedList UserOp.distinct).toEo xs)) :
    CondEquiv Φ ((AppShape.typedList UserOp.distinct).toEo xs)
      ((AppShape.typedList UserOp.distinct).toEo ys) := by
  have hlen := h.length_eq
  simp only [AppShape.toEo] at ht ⊢
  by_cases hle : 2 ≤ xs.length
  · have hle' : 2 ≤ ys.length := hlen ▸ hle
    simp only [hle, hle', ↓reduceIte] at ht ⊢
    -- the same nil
    have hnil : typedNil UserOp._at__at_TypedList_cons (ys.headD Term.Stuck) =
        typedNil UserOp._at__at_TypedList_cons (xs.headD Term.Stuck) := by
      cases h with
      | nil => simp at hle
      | cons hxy _ => exact (CondEquiv.typedNil_congr _ hxy).symm
    rw [hnil]
    generalize xs.headD Term.Stuck = x at ht ⊢
    have hT : SameTypes xs ys := h.imp fun _ _ hxy => hxy.type_eq
    have hE := elem_type_congr (typedNil UserOp._at__at_TypedList_cons x) hT
    have hD := typeof_distinct_congr x hT
    simp only [TL] at hE hD
    have hc : __eo_to_smt_typed_list_elem_type (eoRightAssocNil UserOp._at__at_TypedList_cons
        (typedNil UserOp._at__at_TypedList_cons x) xs) ≠ SmtType.None := by
      intro hc; apply ht
      simp only [eoApp1, __eo_to_smt, native_ite, native_Teq, hc, decide_true, ↓reduceIte]
      exact typeof_none
    have hc' := hE ▸ hc
    simp only [eoApp1, HasSmtType, __eo_to_smt, native_ite, native_Teq, hc, decide_false,
      Bool.false_eq_true, ↓reduceIte] at ht
    refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨?_, ?_⟩, fun M hM hΦM => (trueIn_mkEq_iff M _ _).2 ?_⟩
    · simpa [eoApp1, __eo_to_smt, native_ite, native_Teq, hc] using ht
    · simpa [eoApp1, __eo_to_smt, native_ite, native_Teq, hc, hc'] using hD
    · have hR : RelVals M xs ys := h.imp fun x y hxy => (trueIn_mkEq_iff M x y).1 (hxy.2 M hM hΦM)
      have := eval_distinct_congr M x hR
      unfold eoApp1
      simp only [__eo_to_smt, native_ite, native_Teq, hc, hc', decide_false,
        Bool.false_eq_true, ↓reduceIte, this]
      exact LogosFacts.value_rel_refl _
  · simp only [hle, ↓reduceIte] at ht
    exact absurd typeof_none (by simpa [HasSmtType, __eo_to_smt] using ht)

end Telos
