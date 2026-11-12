import TelosProofs.Equiv
import Cpc.Proofs.RuleSupport.CongSupport

/-!
# Congruence

Replacing the children of a node by equivalent children gives an equivalent node.
This is what lets the rewriter rewrite under operators.

The proof reuses Logos's soundness proof of the CPC `cong` rule
(`Cpc/Proofs/RuleSupport/Cong/`), which is generic over application spines
`(f x₁ … xₙ)` and covers every operator in the signature. What this file adds is
the adapter: our translation (`Telos/Node/ToEo.lean`) produces only a few
`AppShape`s, and each is a spine, or a nest of spines for `:right-assoc-nil`
operators. So there is one case per shape, not per kind, and adding a kind to the
`toEo` table needs no new proof.

Binders (`FORALL`, `EXISTS`) are congruent in their body, with the same variable
list (`Node.Equiv.congr_binder`).
-/

open Eo
open Smtm
open SmtEval
open RuleProofs
open CongSupport

namespace Telos

/-! ## Term-level equivalence -/

/-- What `Node.Equiv` says about translations: `(= a b)` is well typed and true in
every well-formed model. -/
def TermEquiv (a b : Term) : Prop :=
  eo_has_bool_type (mkEq a b) ∧ ∀ M, model_wf M → eo_interprets M (mkEq a b) true

theorem eo_interprets_true_iff (M : SmtModel) (t : Term) :
    eo_interprets M t true ↔
      eo_has_bool_type t ∧ __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true := by
  unfold eo_interprets
  constructor
  · intro h
    cases h with
    | intro_true hty hev => exact ⟨hty, hev⟩
  · rintro ⟨hty, hev⟩
    exact smt_interprets.intro_true _ _ hty hev

theorem termEquiv_iff (a b : Term) :
    TermEquiv a b ↔
      (__smtx_typeof (__eo_to_smt a) ≠ SmtType.None ∧
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b)) ∧
      ∀ M, model_wf M →
        smt_value_rel (__smtx_model_eval M (__eo_to_smt a)) (__smtx_model_eval M (__eo_to_smt b)) := by
  have hBool : eo_has_bool_type (mkEq a b) ↔
      __smtx_typeof (__eo_to_smt a) ≠ SmtType.None ∧
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) := by
    change __smtx_typeof (SmtTerm.eq _ _) = SmtType.Bool ↔ _
    rw [typeof_eq_arm, typeof_eq_eq_bool_iff]
  unfold TermEquiv
  rw [hBool]
  constructor
  · rintro ⟨hty, hM⟩
    refine ⟨hty, fun M hwf => ?_⟩
    have := ((eo_interprets_true_iff M _).1 (hM M hwf)).2
    change __smtx_model_eval M (SmtTerm.eq _ _) = _ at this
    rw [eval_eq_arm] at this
    exact (smt_value_rel_iff_model_eval_eq_true _ _).2 this
  · rintro ⟨hty, hM⟩
    refine ⟨hty, fun M hwf => (eo_interprets_true_iff M _).2 ⟨hBool.2 hty, ?_⟩⟩
    change __smtx_model_eval M (SmtTerm.eq _ _) = _
    rw [eval_eq_arm]
    exact (smt_value_rel_iff_model_eval_eq_true _ _).1 (hM M hwf)

theorem Node.equiv_iff_termEquiv (t s : Node) : t.Equiv s ↔ TermEquiv t.toEo s.toEo := by
  rw [Node.equiv_iff, termEquiv_iff]
  exact ⟨fun ⟨hw, he, hv⟩ => ⟨⟨hw, he⟩, hv⟩, fun ⟨⟨hw, he⟩, hv⟩ => ⟨hw, he, hv⟩⟩

theorem TermEquiv.refl (a : Term) (h : eo_has_smt_translation a) : TermEquiv a a :=
  (termEquiv_iff a a).2 ⟨⟨h, rfl⟩, fun _ _ => smt_value_rel_refl _⟩

theorem TermEquiv.translation {a b : Term} (h : TermEquiv a b) : eo_has_smt_translation a :=
  ((termEquiv_iff a b).1 h).1.1

/-! ## Logos's `cong` lemma

Logos proves `congEvidenceSpine_eq_true` in `Cong/Impl.lean`, but as a private
theorem. This is a copy of its (short) proof, which only combines public lemmas.
Upstream candidate: make it public. -/

theorem congEvidenceSpine_eq_true'
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term) (t rhs : Term) :
    RulePremiseEvidence M premises ->
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    CongEvidenceSpine M premises t rhs ->
    eo_interprets M (mkEq t rhs) true := by
  intro hEvidence hEqBool hSpine
  by_cases hForall :
      ∃ xs body,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body
  · rcases hForall with ⟨xs, body, rfl⟩
    have hTrans :
        RuleProofs.eo_has_smt_translation
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) := by
      have hLeftNN :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
          rhs hEqBool).2
      simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
    have hBinderTypesWf : QuantifierBinderTypesWf xs :=
      quantifierBinderTypesWf_of_forall_translation xs body hTrans
    exact congEvidenceSpine_quantifier_eq_true
      M hM premises UserOp.forall xs body rhs (Or.inl rfl)
      hEvidence hBinderTypesWf hEqBool hSpine
  · by_cases hExists :
        ∃ xs body,
          t = Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body
    · rcases hExists with ⟨xs, body, rfl⟩
      have hTrans :
          RuleProofs.eo_has_smt_translation
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) := by
        have hLeftNN :=
          (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)
            rhs hEqBool).2
        simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
      have hBinderTypesWf : QuantifierBinderTypesWf xs :=
        quantifierBinderTypesWf_of_exists_translation xs body hTrans
      exact congEvidenceSpine_quantifier_eq_true
        M hM premises UserOp.exists xs body rhs (Or.inr rfl)
        hEvidence hBinderTypesWf hEqBool hSpine
    · exact congTrueSpine_eq_true M hM t rhs
        ⟨(fun xs body h => hForall ⟨xs, body, h⟩),
          (fun xs body h => hExists ⟨xs, body, h⟩)⟩ hEqBool
        (congTrueSpine_of_congEvidenceSpine M premises hEvidence hSpine)

/-! ## Spines -/

/-- The equalities `(= xᵢ yᵢ)` that justify a spine. -/
def spinePremises : List Term → List Term → List Term
  | x :: xs, y :: ys => mkEq x y :: spinePremises xs ys
  | _, _ => []

theorem spinePremises_valid {xs ys : List Term} (h : List.Forall₂ TermEquiv xs ys) :
    ∀ p ∈ spinePremises xs ys, ∀ M, model_wf M → eo_interprets M p true := by
  induction h with
  | nil => simp [spinePremises]
  | cons hxy _ ih =>
    intro p hp M hM
    simp only [spinePremises, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hxy.2 M hM
    · exact ih p hp M hM

theorem evidenceSpine_foldl (M : SmtModel) (hM : model_wf M) (P : List Term) :
    ∀ {h₁ h₂ : Term} {xs ys : List Term},
      CongEvidenceSpine M P h₁ h₂ →
      List.Forall₂ TermEquiv xs ys →
      (∀ x y, mkEq x y ∈ spinePremises xs ys → mkEq x y ∈ P) →
      CongEvidenceSpine M P (xs.foldl Term.Apply h₁) (ys.foldl Term.Apply h₂) := by
  intro h₁ h₂ xs ys hh h hsub
  induction h generalizing h₁ h₂ with
  | nil => exact hh
  | @cons x y xs ys hxy _ ih =>
    refine ih (CongEvidenceSpine.app hh (hsub x y (by simp [spinePremises])) (hxy.2 M hM)) ?_
    intro a b hab
    exact hsub a b (by simp [spinePremises, hab])

theorem typeSpine_foldl :
    ∀ {h₁ h₂ : Term} {xs ys : List Term},
      CongTypeSpine h₁ h₂ → List.Forall₂ TermEquiv xs ys →
      CongTypeSpine (xs.foldl Term.Apply h₁) (ys.foldl Term.Apply h₂) := by
  intro h₁ h₂ xs ys hh h
  induction h generalizing h₁ h₂ with
  | nil => exact hh
  | cons hxy _ ih => exact ih (CongTypeSpine.app hh hxy.1)

/-- **Spine congruence**: `(head x₁ … xₙ)` and `(head y₁ … yₙ)` are equivalent when
the arguments are pairwise equivalent and the first is well typed. -/
theorem termEquiv_spine (head : Term) {xs ys : List Term} (h : List.Forall₂ TermEquiv xs ys)
    (ht : eo_has_smt_translation (xs.foldl Term.Apply head)) :
    TermEquiv (xs.foldl Term.Apply head) (ys.foldl Term.Apply head) := by
  have hBool : eo_has_bool_type (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head)) :=
    congTypeSpine_eq_has_bool_type _ _ ht (typeSpine_foldl (CongTypeSpine.refl head) h)
  refine ⟨hBool, fun M hM => ?_⟩
  have hValid := spinePremises_valid h
  refine congEvidenceSpine_eq_true' M hM (spinePremises xs ys) _ _
    ⟨fun p hp => hValid p hp M hM, fun N hN _ p hp => hValid p hp N hN⟩ hBool ?_
  exact evidenceSpine_foldl M hM _ (CongEvidenceSpine.refl head) h (fun _ _ hm => hm)

/-! ## Right-associative operators -/

theorem translation_rest_of_and {x r : Term}
    (h : eo_has_smt_translation (eoApp2 UserOp.and x r)) : eo_has_smt_translation r := by
  unfold eo_has_smt_translation at h ⊢
  change __smtx_typeof (SmtTerm.and _ _) ≠ _ at h
  rw [typeof_and_eq] at h
  intro hr
  apply h
  rw [hr]
  by_cases hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool <;> simp [native_ite, native_Teq, hx]

theorem translation_rest_of_or {x r : Term}
    (h : eo_has_smt_translation (eoApp2 UserOp.or x r)) : eo_has_smt_translation r := by
  unfold eo_has_smt_translation at h ⊢
  change __smtx_typeof (SmtTerm.or _ _) ≠ _ at h
  rw [typeof_or_eq] at h
  intro hr
  apply h
  rw [hr]
  by_cases hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool <;> simp [native_ite, native_Teq, hx]

theorem termEquiv_rightAssocNil (op : UserOp) (nil : Term)
    (hrest : ∀ {x r : Term}, eo_has_smt_translation (eoApp2 op x r) → eo_has_smt_translation r)
    {xs ys : List Term} (h : List.Forall₂ TermEquiv xs ys)
    (ht : eo_has_smt_translation (eoRightAssocNil op nil xs)) :
    TermEquiv (eoRightAssocNil op nil xs) (eoRightAssocNil op nil ys) := by
  induction h with
  | nil => exact TermEquiv.refl _ ht
  | @cons x y xs ys hxy hxs ih =>
    have ihr := ih (hrest ht)
    exact termEquiv_spine (Term.UOp op) (xs := [x, eoRightAssocNil op nil xs])
      (ys := [y, eoRightAssocNil op nil ys]) (.cons hxy (.cons ihr .nil)) ht

/-! ## Nodes -/

theorem not_translation_stuck : ¬ eo_has_smt_translation Term.Stuck := by
  simp [eo_has_smt_translation]; rfl

theorem shape_congr (sh : AppShape) (hsh : sh.isChildCongruent = true) {xs ys : List Term}
    (h : List.Forall₂ TermEquiv xs ys) (ht : eo_has_smt_translation (sh.toEo xs)) :
    TermEquiv (sh.toEo xs) (sh.toEo ys) := by
  have hlen := h.length_eq
  cases sh with
  | spine head arity =>
    by_cases hacc : arity.accepts xs.length = true
    · have hacc' : arity.accepts ys.length = true := hlen ▸ hacc
      rw [AppShape.toEo, ite_eq_left hacc] at ht
      rw [AppShape.toEo, AppShape.toEo, ite_eq_left hacc, ite_eq_left hacc']
      exact termEquiv_spine head h ht
    · rw [AppShape.toEo, ite_eq_right hacc] at ht
      exact absurd ht not_translation_stuck
  | rightAssocNil op nil =>
    simp only [AppShape.isChildCongruent, Bool.or_eq_true, beq_iff_eq] at hsh
    by_cases hle : 2 ≤ xs.length
    · have hle' : 2 ≤ ys.length := hlen ▸ hle
      rw [AppShape.toEo, ite_eq_left hle] at ht
      rw [AppShape.toEo, AppShape.toEo, ite_eq_left hle, ite_eq_left hle']
      rcases hsh with rfl | rfl
      · exact termEquiv_rightAssocNil _ _ translation_rest_of_and h ht
      · exact termEquiv_rightAssocNil _ _ translation_rest_of_or h ht
    · rw [AppShape.toEo, ite_eq_right hle] at ht
      exact absurd ht not_translation_stuck
  | binderList => simp [AppShape.isChildCongruent] at hsh
  | binder _ => simp [AppShape.isChildCongruent] at hsh
  | none => exact absurd ht not_translation_stuck

/-- **Congruence of `Node.Equiv`.** For an operator whose shape is congruent child
by child (every operator except binders), equivalent children give an equivalent
node. -/
theorem Node.Equiv.congr {op : Op} (hop : op.eoShape.isChildCongruent = true)
    {cs ds : Array Node} (hwt : (Node.app op cs).WellTyped)
    (h : List.Forall₂ Node.Equiv cs.toList ds.toList) :
    (Node.app op cs).Equiv (Node.app op ds) := by
  rw [Node.equiv_iff_termEquiv, Node.toEo_app, Node.toEo_app]
  have hwt' : eo_has_smt_translation (op.eoShape.toEo (cs.toList.map Node.toEo)) := by
    have := hwt
    unfold Node.WellTyped Node.smtType Node.toSmt at this
    rw [Node.toEo_app] at this
    exact this
  refine shape_congr _ hop ?_ hwt'
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ hcd => (Node.equiv_iff_termEquiv _ _).1 hcd

/-- **Congruence under a binder.** A quantifier with an equivalent body (and the
same variables) is equivalent. Instantiation patterns may differ, since they carry
no semantics. -/
theorem Node.Equiv.congr_binder {k : Kind} (hk : k = .FORALL ∨ k = .EXISTS)
    {vs body body' : Node} {pats pats' : List Node} (hp : pats.length = pats'.length)
    (hwt : (Node.app (.kind k) ⟨vs :: body :: pats⟩).WellTyped) (h : body.Equiv body') :
    (Node.app (.kind k) ⟨vs :: body :: pats⟩).Equiv (Node.app (.kind k) ⟨vs :: body' :: pats'⟩) := by
  rw [Node.equiv_iff_termEquiv, Node.toEo_app, Node.toEo_app]
  have hwt' := hwt
  unfold Node.WellTyped Node.smtType Node.toSmt at hwt'
  rw [Node.toEo_app] at hwt'
  have hb := (Node.equiv_iff_termEquiv _ _).1 h
  rcases hk with rfl | rfl <;>
  · rcases pats with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> rcases pats' with _ | ⟨p', _ | ⟨_, _⟩⟩ <;>
      simp at hp
    all_goals
      simp only [Op.eoShape, Kind.eoShape, AppShape.toEo, List.map] at hwt' ⊢
      first
      | exact absurd hwt' not_translation_stuck
      | exact termEquiv_spine (Term.Apply (Term.UOp _) vs.toEo) (xs := [body.toEo])
          (ys := [body'.toEo]) (.cons hb .nil) hwt'

end Telos
