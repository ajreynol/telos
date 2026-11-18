import TelosProofs.Core.Congruence

/-!
# Equivalence under a condition

`CondEquiv Φ a b`: `(= a b)` is well typed, and true in every well-formed model
that satisfies `Φ`. Substituting the sides of equations that hold in a model
(non-clausal simplification) gives terms that are equal in that model, not
equivalent: the conjunction step that does it (`Telos/Core/Certified.lean`,
`Certified.tri`) relates conjuncts by `CondEquiv`.

A condition used for congruence must be *stable*: preserved by changing the
values of variables (`AgreesOnGlobals`), since Logos's congruence in one model
(`LogosFacts.cong_spine_model`) asks for argument equalities that are true in
every model agreeing with it on the globals. A condition made of closed
formulas is stable (`LogosFacts.closed_eval`).

Congruence is proven as in `Congruence.lean`: one case per `AppShape`, for the
shapes that are not quantifiers.
-/

open Eo Smtm SmtEval

namespace Telos

set_option linter.unusedSectionVars false

variable [LogosFacts]

/-- A condition on models that is preserved by changing the values of variables. -/
def StableCond (Φ : SmtModel → Prop) : Prop :=
  ∀ M N, model_wf M → model_wf N → AgreesOnGlobals M N → Φ M → Φ N

/-- `(= a b)` is well typed, and true in every well-formed model satisfying `Φ`. -/
def CondEquiv (Φ : SmtModel → Prop) (a b : Term) : Prop :=
  HasBoolType (mkEq a b) ∧ ∀ M, model_wf M → Φ M → TrueIn M (mkEq a b)

theorem hasBoolType_mkEq_iff (a b : Term) :
    HasBoolType (mkEq a b) ↔
      __smtx_typeof (__eo_to_smt a) ≠ SmtType.None ∧
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) := by
  unfold HasBoolType
  change __smtx_typeof (SmtTerm.eq _ _) = _ ↔ _
  rw [typeof_eq_eq, typeof_eq_eq_bool_iff]

theorem trueIn_mkEq_iff (M : SmtModel) (a b : Term) :
    TrueIn M (mkEq a b) ↔
      SmtValueRel (__smtx_model_eval M (__eo_to_smt a)) (__smtx_model_eval M (__eo_to_smt b)) := by
  unfold TrueIn
  change __smtx_model_eval M (SmtTerm.eq _ _) = _ ↔ _
  rw [model_eval_eq_eq]
  rfl

namespace CondEquiv

variable {Φ : SmtModel → Prop}

theorem typed_left {a b : Term} (h : CondEquiv Φ a b) : HasSmtType a :=
  ((hasBoolType_mkEq_iff a b).1 h.1).1

theorem type_eq {a b : Term} (h : CondEquiv Φ a b) :
    __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) :=
  ((hasBoolType_mkEq_iff a b).1 h.1).2

theorem typed_right {a b : Term} (h : CondEquiv Φ a b) : HasSmtType b := by
  intro hb; exact h.typed_left (h.type_eq.trans hb)

theorem refl (a : Term) (h : HasSmtType a) : CondEquiv Φ a a :=
  ⟨(hasBoolType_mkEq_iff a a).2 ⟨h, rfl⟩,
    fun M _ _ => (trueIn_mkEq_iff M a a).2 (LogosFacts.value_rel_refl _)⟩

theorem trans {a b c : Term} (h₁ : CondEquiv Φ a b) (h₂ : CondEquiv Φ b c) : CondEquiv Φ a c :=
  ⟨(hasBoolType_mkEq_iff a c).2 ⟨h₁.typed_left, h₁.type_eq.trans h₂.type_eq⟩,
    fun M hM hΦ => (trueIn_mkEq_iff M a c).2 (LogosFacts.value_rel_trans _ _ _
      ((trueIn_mkEq_iff M a b).1 (h₁.2 M hM hΦ)) ((trueIn_mkEq_iff M b c).1 (h₂.2 M hM hΦ)))⟩

/-- An equivalence holds under any condition. -/
theorem of_termEquiv {a b : Term} (h : TermEquiv a b) : CondEquiv Φ a b := by
  obtain ⟨⟨hT, hE⟩, hV⟩ := (termEquiv_iff a b).1 h
  exact ⟨(hasBoolType_mkEq_iff a b).2 ⟨hT, hE⟩, fun M hM _ => (trueIn_mkEq_iff M a b).2 (hV M hM)⟩

theorem of_equiv {t s : Node} (h : t.Equiv s) : CondEquiv Φ t.toEo s.toEo :=
  of_termEquiv ((Node.equiv_iff_termEquiv t s).1 h)

/-- Equal types give a typed-nil operator the same nil. -/
theorem typedNil_congr (op : UserOp) {x y : Term} (h : CondEquiv Φ x y) :
    typedNil op x = typedNil op y := by
  unfold typedNil; rw [h.type_eq]

end CondEquiv

/-! ## Spines -/

/-- **Spine congruence under a stable condition.** -/
theorem condEquiv_spine {Φ : SmtModel → Prop} (hΦ : StableCond Φ) (head : Term)
    {xs ys : List Term} (h : List.Forall₂ (CondEquiv Φ) xs ys)
    (ht : HasSmtType (xs.foldl Term.Apply head))
    (hq : NotTopLevelQuantifier (xs.foldl Term.Apply head)) :
    CondEquiv Φ (xs.foldl Term.Apply head) (ys.foldl Term.Apply head) := by
  have hTy := LogosFacts.cong_type_spine head xs ys ht (h.imp fun _ _ hxy => hxy.1)
  refine ⟨hTy, fun M hM hΦM => ?_⟩
  refine LogosFacts.cong_spine_model M hM head xs ys hq hTy (h.imp fun x y hxy => ⟨hxy.1, ?_⟩)
  intro N hN hAgree
  exact hxy.2 N hN (hΦ M N hM hN hAgree hΦM)

/-- An application `(op x r)` of a non-quantifier operator is not a quantifier. -/
theorem notTopLevelQuantifier_app2 {op : UserOp} (hf : op ≠ UserOp.forall)
    (he : op ≠ UserOp.exists) (x r : Term) : NotTopLevelQuantifier (eoApp2 op x r) := by
  refine ⟨fun xs body h => ?_, fun xs body h => ?_⟩ <;>
    (simp only [eoApp2, Term.Apply.injEq, Term.UOp.injEq] at h; exact absurd h.1.1 ‹_›)

theorem condEquiv_rightAssocNil {Φ : SmtModel → Prop} (hΦ : StableCond Φ) (op : UserOp)
    (hf : op ≠ UserOp.forall) (he : op ≠ UserOp.exists) (nil : Term)
    (hrest : ∀ {x r : Term}, HasSmtType (eoApp2 op x r) → HasSmtType r)
    {xs ys : List Term} (h : List.Forall₂ (CondEquiv Φ) xs ys)
    (ht : HasSmtType (eoRightAssocNil op nil xs)) :
    CondEquiv Φ (eoRightAssocNil op nil xs) (eoRightAssocNil op nil ys) := by
  induction h with
  | nil => exact CondEquiv.refl _ ht
  | @cons x y xs ys hxy hxs ih =>
    have ihr := ih (hrest ht)
    exact condEquiv_spine hΦ (Term.UOp op) (xs := [x, eoRightAssocNil op nil xs])
      (ys := [y, eoRightAssocNil op nil ys]) (.cons hxy (.cons ihr .nil)) ht
      (notTopLevelQuantifier_app2 hf he _ _)

end Telos
