import TelosProofs.Equiv
import Cpc.Proofs.RuleSupport.Cong.Spine
import Cpc.Proofs.RuleSupport.SpineArgsSupport

/-!
# Congruence

Replacing the children of a node by equivalent children gives an equivalent node.
This is what lets the rewriter rewrite under operators.

The proof reuses Logos's model-free spine congruence `cong_spine_valid`
(`Cpc/Proofs/RuleSupport/Cong/Spine.lean`, from its proof of the CPC `cong`
rule), which is generic over application spines `(f x₁ … xₙ)` and covers every
operator in the signature. What this file adds is
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

theorem termEquiv_iff (a b : Term) :
    TermEquiv a b ↔
      (__smtx_typeof (__eo_to_smt a) ≠ SmtType.None ∧
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b)) ∧
      ∀ M, model_wf M →
        smt_value_rel (__smtx_model_eval M (__eo_to_smt a)) (__smtx_model_eval M (__eo_to_smt b)) :=
  eq_valid_iff a b

theorem Node.equiv_iff_termEquiv (t s : Node) : t.Equiv s ↔ TermEquiv t.toEo s.toEo := by
  rw [Node.equiv_iff, termEquiv_iff]
  exact ⟨fun ⟨hw, he, hv⟩ => ⟨⟨hw, he⟩, hv⟩, fun ⟨⟨hw, he⟩, hv⟩ => ⟨hw, he, hv⟩⟩

theorem TermEquiv.refl (a : Term) (h : eo_has_smt_translation a) : TermEquiv a a :=
  (termEquiv_iff a a).2 ⟨⟨h, rfl⟩, fun _ _ => smt_value_rel_refl _⟩

theorem TermEquiv.translation {a b : Term} (h : TermEquiv a b) : eo_has_smt_translation a :=
  ((termEquiv_iff a b).1 h).1.1

/-! ## Spines -/

/-- **Spine congruence** (Logos's `cong_spine_valid`): `(head x₁ … xₙ)` and
`(head y₁ … yₙ)` are equivalent when the arguments are pairwise equivalent and the
first is well typed. -/
theorem termEquiv_spine (head : Term) {xs ys : List Term} (h : List.Forall₂ TermEquiv xs ys)
    (ht : eo_has_smt_translation (xs.foldl Term.Apply head)) :
    TermEquiv (xs.foldl Term.Apply head) (ys.foldl Term.Apply head) :=
  cong_spine_valid head xs ys ht h

/-! ## Right-associative operators -/

/-- The tail of a well-typed `(and x r)` or `(or x r)` is well typed. -/
theorem translation_rest {op : UserOp} (hop : op = UserOp.and ∨ op = UserOp.or) {x r : Term}
    (h : eo_has_smt_translation (eoApp2 op x r)) : eo_has_smt_translation r := by
  have hHead : SpineArgsSupport.SpineArgsHead (Term.UOp op) [x, r].length := by
    rcases hop with rfl | rfl
    exacts [.and, .or]
  exact SpineArgsSupport.spine_args_have_smt_translation _ [x, r] hHead h r (by simp)

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
      exact termEquiv_rightAssocNil _ _ (translation_rest hsh) h ht
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
