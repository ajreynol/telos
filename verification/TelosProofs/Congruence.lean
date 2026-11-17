import TelosProofs.Equiv

/-!
# Congruence

Replacing the children of a node by equivalent children gives an equivalent node.
This is what lets the rewriter rewrite under operators.

The proof reuses Logos's model-free spine congruence `cong_spine_valid`
(`Cpc/Proofs/RuleSupport/Cong/Spine.lean`, from its proof of the CPC `cong`
rule; `LogosFacts.cong_spine` here), which is generic over application spines `(f x₁ … xₙ)` and covers every
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

namespace Telos

-- Most theorems here use Logos's facts (`LogosFacts`); the others ignore them.
set_option linter.unusedSectionVars false

variable [LogosFacts]

/-! ## Term-level equivalence -/

/-- What `Node.Equiv` says about translations: `(= a b)` is well typed and true in
every well-formed model. -/
def TermEquiv (a b : Term) : Prop := Valid (mkEq a b)

theorem termEquiv_iff (a b : Term) :
    TermEquiv a b ↔
      (__smtx_typeof (__eo_to_smt a) ≠ SmtType.None ∧
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b)) ∧
      ∀ M, model_wf M →
        SmtValueRel (__smtx_model_eval M (__eo_to_smt a)) (__smtx_model_eval M (__eo_to_smt b)) :=
  LogosFacts.eq_valid_iff a b

theorem Node.equiv_iff_termEquiv (t s : Node) : t.Equiv s ↔ TermEquiv t.toEo s.toEo := by
  rw [Node.equiv_iff, termEquiv_iff]
  exact ⟨fun ⟨hw, he, hv⟩ => ⟨⟨hw, he⟩, hv⟩, fun ⟨⟨hw, he⟩, hv⟩ => ⟨hw, he, hv⟩⟩

theorem TermEquiv.refl (a : Term) (h : HasSmtType a) : TermEquiv a a :=
  (termEquiv_iff a a).2 ⟨⟨h, rfl⟩, fun _ _ => LogosFacts.value_rel_refl _⟩

theorem TermEquiv.translation {a b : Term} (h : TermEquiv a b) : HasSmtType a :=
  ((termEquiv_iff a b).1 h).1.1

/-! ## Spines -/

/-- **Spine congruence** (Logos's `cong_spine_valid`): `(head x₁ … xₙ)` and
`(head y₁ … yₙ)` are equivalent when the arguments are pairwise equivalent and the
first is well typed. -/
theorem termEquiv_spine (head : Term) {xs ys : List Term} (h : List.Forall₂ TermEquiv xs ys)
    (ht : HasSmtType (xs.foldl Term.Apply head)) :
    TermEquiv (xs.foldl Term.Apply head) (ys.foldl Term.Apply head) :=
  LogosFacts.cong_spine head xs ys ht h

/-! ## Right-associative operators -/

/-- The tail of a well-typed `(and x r)` or `(or x r)` is well typed. -/
theorem translation_rest {op : UserOp} (hop : op = UserOp.and ∨ op = UserOp.or) {x r : Term}
    (h : HasSmtType (eoApp2 op x r)) : HasSmtType r :=
  LogosFacts.and_or_rest op x r hop h

/-- The tail of a well-typed `(+ x r)` or `(* x r)` is well typed. -/
theorem translation_rest_arith {op : UserOp} (hop : op = UserOp.plus ∨ op = UserOp.mult)
    {x r : Term} (h : HasSmtType (eoApp2 op x r)) : HasSmtType r := by
  have key : ∀ {T U : SmtType}, __smtx_typeof_arith_overload_op_2 T U ≠ SmtType.None →
      U ≠ SmtType.None := by
    intro T U h hU
    subst hU
    cases T <;> exact h rfl
  unfold HasSmtType at h ⊢
  rcases hop with rfl | rfl
  · change __smtx_typeof (SmtTerm.plus _ _) ≠ _ at h
    rw [typeof_plus_eq] at h
    exact key h
  · change __smtx_typeof (SmtTerm.mult _ _) ≠ _ at h
    rw [typeof_mult_eq] at h
    exact key h

/-- Equivalent first elements give a typed-nil operator the same nil: the nil
depends only on the SMT type, which equivalent terms share. -/
theorem typedNil_congr (op : UserOp) {x y : Term} (h : TermEquiv x y) :
    typedNil op x = typedNil op y := by
  obtain ⟨⟨_, heq⟩, _⟩ := (termEquiv_iff x y).1 h
  unfold typedNil
  rw [heq]

/-! ## Bit-vector operators -/

theorem typeof_bvand' (a b : SmtTerm) : __smtx_typeof (SmtTerm.bvand a b) =
    __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]
theorem typeof_bvor' (a b : SmtTerm) : __smtx_typeof (SmtTerm.bvor a b) =
    __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]
theorem typeof_bvxor' (a b : SmtTerm) : __smtx_typeof (SmtTerm.bvxor a b) =
    __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]
theorem typeof_bvadd' (a b : SmtTerm) : __smtx_typeof (SmtTerm.bvadd a b) =
    __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]
theorem typeof_bvmul' (a b : SmtTerm) : __smtx_typeof (SmtTerm.bvmul a b) =
    __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

theorem bv_op_2_args {T U : SmtType} (h : __smtx_typeof_bv_op_2 T U ≠ SmtType.None) :
    (∃ w, T = SmtType.BitVec w) ∧ U ≠ SmtType.None := by
  cases T <;> cases U <;> simp_all [__smtx_typeof_bv_op_2]

theorem concat_args {T U : SmtType} (h : __smtx_typeof_concat T U ≠ SmtType.None) :
    (∃ w, T = SmtType.BitVec w) ∧ U ≠ SmtType.None := by
  cases T <;> cases U <;> simp_all [__smtx_typeof_concat]

/-- A well-typed application of a `:right-assoc-nil` bit-vector operator has a
bit-vector first argument and a well-typed tail. -/
theorem bv_nary_args {op : UserOp} (hop : op.isBvNary = true) {x r : Term}
    (h : HasSmtType (eoApp2 op x r)) :
    (∃ w, __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) ∧ HasSmtType r := by
  unfold HasSmtType at h ⊢
  simp only [UserOp.isBvNary, Bool.or_eq_true, beq_iff_eq] at hop
  rcases hop with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl
  · change __smtx_typeof (SmtTerm.concat _ _) ≠ _ at h
    rw [typeof_concat_eq] at h; exact concat_args h
  · change __smtx_typeof (SmtTerm.bvand _ _) ≠ _ at h
    rw [typeof_bvand'] at h; exact bv_op_2_args h
  · change __smtx_typeof (SmtTerm.bvor _ _) ≠ _ at h
    rw [typeof_bvor'] at h; exact bv_op_2_args h
  · change __smtx_typeof (SmtTerm.bvxor _ _) ≠ _ at h
    rw [typeof_bvxor'] at h; exact bv_op_2_args h
  · change __smtx_typeof (SmtTerm.bvadd _ _) ≠ _ at h
    rw [typeof_bvadd'] at h; exact bv_op_2_args h
  · change __smtx_typeof (SmtTerm.bvmul _ _) ≠ _ at h
    rw [typeof_bvmul'] at h; exact bv_op_2_args h

/-! ## Strings and regular expressions -/

theorem typeof_str_concat' (a b : SmtTerm) : __smtx_typeof (SmtTerm.str_concat a b) =
    __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

theorem seq_op_2_args {T U : SmtType} (h : __smtx_typeof_seq_op_2 T U ≠ SmtType.None) :
    (∃ A, T = SmtType.Seq A) ∧ U ≠ SmtType.None := by
  cases T <;> cases U <;> simp_all [__smtx_typeof_seq_op_2]

/-- A well-typed application of a typed-nil operator (`isTypedNary`) has a first
argument of a well-formed type, and a well-typed tail. -/
theorem typed_nary_args {op : UserOp} (hop : op.isTypedNary = true) {x r : Term}
    (h : HasSmtType (eoApp2 op x r)) :
    __smtx_type_wf (__smtx_typeof (__eo_to_smt x)) = true ∧ HasSmtType r := by
  simp only [UserOp.isTypedNary, Bool.or_eq_true, beq_iff_eq] at hop
  rcases hop with hbv | rfl
  · obtain ⟨⟨w, hw⟩, hr⟩ := bv_nary_args hbv h
    refine ⟨?_, hr⟩
    rw [hw]; simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec, SmtEval.native_and]
  · unfold HasSmtType at h ⊢
    change __smtx_typeof (SmtTerm.str_concat _ _) ≠ _ at h
    rw [typeof_str_concat'] at h
    obtain ⟨⟨A, hA⟩, hU⟩ := seq_op_2_args h
    refine ⟨?_, hU⟩
    rw [hA]
    exact LogosFacts.seq_type_wf _ _ (by rw [hA]; simp) hA

/-- The tail of a well-typed `re.++`, `re.inter` or `re.union` is well typed. -/
theorem translation_rest_re {op : UserOp} (hop : op.isReNary = true) {x r : Term}
    (h : HasSmtType (eoApp2 op x r)) : HasSmtType r := by
  unfold HasSmtType at h ⊢
  simp only [UserOp.isReNary, Bool.or_eq_true, beq_iff_eq] at hop
  intro hr
  apply h
  rcases hop with (rfl | rfl) | rfl
  · change __smtx_typeof (SmtTerm.re_concat _ _) = _
    rw [__smtx_typeof.eq_def]; simp only; rw [hr]; simp [native_ite, native_Teq]
  · change __smtx_typeof (SmtTerm.re_inter _ _) = _
    rw [__smtx_typeof.eq_def]; simp only; rw [hr]; simp [native_ite, native_Teq]
  · change __smtx_typeof (SmtTerm.re_union _ _) = _
    rw [__smtx_typeof.eq_def]; simp only; rw [hr]; simp [native_ite, native_Teq]

theorem termEquiv_rightAssocNil (op : UserOp) (nil : Term)
    (hrest : ∀ {x r : Term}, HasSmtType (eoApp2 op x r) → HasSmtType r)
    {xs ys : List Term} (h : List.Forall₂ TermEquiv xs ys)
    (ht : HasSmtType (eoRightAssocNil op nil xs)) :
    TermEquiv (eoRightAssocNil op nil xs) (eoRightAssocNil op nil ys) := by
  induction h with
  | nil => exact TermEquiv.refl _ ht
  | @cons x y xs ys hxy hxs ih =>
    have ihr := ih (hrest ht)
    exact termEquiv_spine (Term.UOp op) (xs := [x, eoRightAssocNil op nil xs])
      (ys := [y, eoRightAssocNil op nil ys]) (.cons hxy (.cons ihr .nil)) ht

/-! ## Nodes -/

theorem not_translation_stuck : ¬ HasSmtType Term.Stuck := by
  simp [HasSmtType]; rfl

theorem shape_congr (sh : AppShape) (hsh : sh.isChildCongruent = true) {xs ys : List Term}
    (h : List.Forall₂ TermEquiv xs ys) (ht : HasSmtType (sh.toEo xs)) :
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
    by_cases hle : 2 ≤ xs.length
    · have hle' : 2 ≤ ys.length := hlen ▸ hle
      rw [AppShape.toEo, ite_eq_left hle] at ht
      rw [AppShape.toEo, AppShape.toEo, ite_eq_left hle, ite_eq_left hle']
      have hnil : nil.eval op (ys.headD Term.Stuck) = nil.eval op (xs.headD Term.Stuck) := by
        cases nil with
        | const _ => rfl
        | typed =>
          cases h with
          | nil => simp at hle
          | cons hxy _ => exact (typedNil_congr op hxy).symm
      rw [hnil]
      have hrest : ∀ {x r : Term}, HasSmtType (eoApp2 op x r) →
          HasSmtType r := by
        cases nil with
        | const _ =>
          simp only [AppShape.isChildCongruent, Bool.or_eq_true, beq_iff_eq] at hsh
          rcases hsh with hsh | hre
          · exact translation_rest hsh
          · exact translation_rest_re hre
        | typed =>
          simp only [AppShape.isChildCongruent, Bool.or_eq_true, beq_iff_eq] at hsh
          rcases hsh with hsh | hbv
          · exact translation_rest_arith hsh
          · exact fun h => (typed_nary_args hbv h).2
      exact termEquiv_rightAssocNil _ _ hrest h ht
    · rw [AppShape.toEo, ite_eq_right hle] at ht
      exact absurd ht not_translation_stuck
  | typedList _ => simp [AppShape.isChildCongruent] at hsh
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
  have hwt' : HasSmtType (op.eoShape.toEo (cs.toList.map Node.toEo)) := by
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
