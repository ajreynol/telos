import Telos.Core.Certified
import TelosProofs.Core.LogosFacts
import TelosProofs.Core.DistinctCong

/-!
# Children of well-typed applications are well typed

For every operator of `Op.childrenTypedOfParent` (all but binders, and some
applications of terms), an application whose translation has an SMT type has arguments
whose translations have SMT types. So the congruence steps of the driver need no
run-time check that the children are well typed, and substitution
(`Certified.tri`) may go below these operators: `Certified.equiv` and
`tri_equiv` derive it from the parent (`children_wellTyped`).

Most operators translate to an SMT term whose typing rule is `None` as soon
as an argument's type is: `typed1` and `typedN` unfold the translation and
the typing rule with that argument's type `None`. The others compare an
argument's type with a component of another's (`select`, `store`,
`set.member`), which is not `None` (`LogosFacts.type_no_none`), or go
through the translation of datatypes and tuples, for which the Logos theorems
are restated (`LogosFacts`).
-/

open Eo Smtm SmtEval

namespace Telos.ChildTyping

/-- `t`'s translation has an SMT type. -/
abbrev Typed (t : Term) : Prop := HasSmtType t

/-- Close a goal `rule … = None` where an argument type is `None`. -/
macro "fin_none" : tactic => `(tactic| first
  | rfl
  | (simp [native_ite, native_Teq, native_and, native_or, native_not, native_zleq, native_zeq,
      native_zlt, native_mod_total, native_int_pow2, native_int_to_nat, native_zexp_total, __smtx_type_wf,
      __smtx_type_wf_rec, __smtx_type_wf_component, __smtx_index_typeof_map, __smtx_map_to_set_type, __smtx_typeof_apply, __smtx_typeof_apply_value, __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_1_ret, __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret, __smtx_typeof_concat, __smtx_typeof_dt_cons_rec, __smtx_typeof_dt_cons_value_rec, __smtx_typeof_eq, __smtx_typeof_extract, __smtx_typeof_guard, __smtx_typeof_guard_wf, __smtx_typeof_int_to_bv, __smtx_typeof_ite, __smtx_typeof_map_diff, __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_repeat, __smtx_typeof_rotate_left, __smtx_typeof_rotate_right, __smtx_typeof_select, __smtx_typeof_seq_diff, __smtx_typeof_seq_nth, __smtx_typeof_seq_op_1, __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2, __smtx_typeof_seq_op_2_ret, __smtx_typeof_seq_op_3, __smtx_typeof_set_member, __smtx_typeof_sets_op_2, __smtx_typeof_sets_op_2_ret, __smtx_typeof_sign_extend, __smtx_typeof_store, __smtx_typeof_str_at, __smtx_typeof_str_indexof, __smtx_typeof_str_substr, __smtx_typeof_str_update, __smtx_typeof_zero_extend]; done)
  | ((repeat' split) <;> simp_all [native_ite, native_Teq, native_and, native_or, native_not,
      native_zleq, native_zeq, native_zlt, native_mod_total, native_int_pow2, native_int_to_nat, native_zexp_total,
      __smtx_type_wf, __smtx_type_wf_rec, __smtx_type_wf_component, __smtx_index_typeof_map, __smtx_map_to_set_type, __smtx_typeof_apply, __smtx_typeof_apply_value, __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_1_ret, __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret, __smtx_typeof_concat, __smtx_typeof_dt_cons_rec, __smtx_typeof_dt_cons_value_rec, __smtx_typeof_eq, __smtx_typeof_extract, __smtx_typeof_guard, __smtx_typeof_guard_wf, __smtx_typeof_int_to_bv, __smtx_typeof_ite, __smtx_typeof_map_diff, __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_repeat, __smtx_typeof_rotate_left, __smtx_typeof_rotate_right, __smtx_typeof_select, __smtx_typeof_seq_diff, __smtx_typeof_seq_nth, __smtx_typeof_seq_op_1, __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2, __smtx_typeof_seq_op_2_ret, __smtx_typeof_seq_op_3, __smtx_typeof_set_member, __smtx_typeof_sets_op_2, __smtx_typeof_sets_op_2_ret, __smtx_typeof_sign_extend, __smtx_typeof_store, __smtx_typeof_str_at, __smtx_typeof_str_indexof, __smtx_typeof_str_substr, __smtx_typeof_str_update, __smtx_typeof_zero_extend]; done))

set_option hygiene false in
/-- `Typed x` from `h : Typed (op x)`, for an operator whose typing rule is
`None` on an ill-typed argument. -/
macro "typed1" : tactic => `(tactic| (unfold Typed HasSmtType at *; intro hx; apply h; simp only [__eo_to_smt, __smtx_typeof, hx]; fin_none))

set_option hygiene false in
/-- `typed1`, for each argument of an operator with two or three. -/
macro "typedN" : tactic => `(tactic| (unfold Typed HasSmtType at *; refine ⟨?_, ?_⟩ <;> (try refine ⟨?_, ?_⟩) <;> (intro hx; apply h; simp only [__eo_to_smt, __smtx_typeof, hx]; fin_none)))

theorem typed_stuck : ¬ Typed .Stuck := by
  unfold Typed HasSmtType; rw [show __eo_to_smt .Stuck = SmtTerm.None from rfl, __smtx_typeof.eq_def]; simp

theorem ne_none_of_noNone {T : SmtType} (h : NoNoneParts T) : T ≠ SmtType.None := by
  rintro rfl; exact h

/-- The components of the type of a well-typed term are not `None`. -/
theorem noNone_of_typeof [LogosFacts] {t : SmtTerm} {T : SmtType} (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) : NoNoneParts T := by
  have := LogosFacts.type_no_none t (by rw [h]; exact hT); rwa [h] at this

theorem typed_select [LogosFacts] (x y : Term) (h : Typed (.Apply (.Apply (.UOp .select) x) y)) :
    Typed x ∧ Typed y := by
  unfold Typed HasSmtType at *
  refine ⟨?_, ?_⟩ <;> intro hx <;> apply h <;> simp only [__eo_to_smt, __smtx_typeof, hx]
  · rfl
  · cases hT : __smtx_typeof (__eo_to_smt x) <;> simp [__smtx_typeof_select]
    rename_i A B
    have := noNone_of_typeof hT (by simp)
    simp only [NoNoneParts] at this
    simp [native_ite, native_Teq, ne_none_of_noNone this.1]

theorem typed_store [LogosFacts] (x y z : Term) (h : Typed (.Apply (.Apply (.Apply (.UOp .store) x) y) z)) :
    Typed x ∧ Typed y ∧ Typed z := by
  unfold Typed HasSmtType at *
  refine ⟨?_, ?_, ?_⟩ <;> intro hx <;> apply h <;> simp only [__eo_to_smt, __smtx_typeof, hx]
  · rfl
  all_goals
    cases hT : __smtx_typeof (__eo_to_smt x) <;> simp [__smtx_typeof_store]
    rename_i A B
    have := noNone_of_typeof hT (by simp)
    simp only [NoNoneParts] at this
    simp [native_ite, native_Teq, ne_none_of_noNone this.1, ne_none_of_noNone this.2]

theorem typed_set_member [LogosFacts] (x y : Term) (h : Typed (.Apply (.Apply (.UOp .set_member) x) y)) :
    Typed x ∧ Typed y := by
  unfold Typed HasSmtType at *
  refine ⟨?_, ?_⟩ <;> intro hx <;> apply h <;> simp only [__eo_to_smt, __smtx_typeof, hx]
  · cases hT : __smtx_typeof (__eo_to_smt y) <;> simp [__smtx_typeof_set_member]
    rename_i A
    have := noNone_of_typeof hT (by simp)
    simp only [NoNoneParts] at this
    simp [native_ite, native_Teq, (ne_none_of_noNone this).symm]
  · simp [__smtx_typeof_set_member]

theorem typed_ite (x y z : Term) (h : Typed (.Apply (.Apply (.Apply (.UOp .ite) x) y) z)) :
    Typed x ∧ Typed y ∧ Typed z := by
  unfold Typed HasSmtType at *
  refine ⟨?_, ?_, ?_⟩ <;> intro hx <;> apply h <;> simp only [__eo_to_smt, __smtx_typeof, hx]
  · fin_none
  · cases __smtx_typeof (__eo_to_smt x) <;> cases __smtx_typeof (__eo_to_smt z) <;> fin_none
  · cases __smtx_typeof (__eo_to_smt x) <;> cases __smtx_typeof (__eo_to_smt y) <;> fin_none

theorem typed_bvite (x y z : Term) (h : Typed (.Apply (.Apply (.Apply (.UOp .bvite) x) y) z)) :
    Typed x ∧ Typed y ∧ Typed z := by
  unfold Typed HasSmtType at *
  refine ⟨?_, ?_, ?_⟩ <;> intro hx <;> apply h <;> simp only [__eo_to_smt, __smtx_typeof, hx]
  · fin_none
  · cases __smtx_typeof (__eo_to_smt x) <;> cases __smtx_typeof (__eo_to_smt z) <;>
      simp only [native_ite, native_Teq, native_zexp_total, native_mod_total, native_zeq, native_zleq,
        native_int_pow2, native_int_to_nat, __smtx_typeof_eq, __smtx_typeof_guard] <;>
      (try split_ifs) <;> simp_all [__smtx_typeof_ite, native_ite, native_Teq, native_and]
  · cases __smtx_typeof (__eo_to_smt x) <;> cases __smtx_typeof (__eo_to_smt y) <;>
      simp only [native_ite, native_Teq, native_zexp_total, native_mod_total, native_zeq, native_zleq,
        native_int_pow2, native_int_to_nat, __smtx_typeof_eq, __smtx_typeof_guard] <;>
      (try split_ifs) <;> simp_all [__smtx_typeof_ite, native_ite, native_Teq, native_and]

theorem spine0 {head : Term} :
    ∀ xs : List Term, Typed ((AppShape.spine head (.exactly 0)).toEo xs) → ∀ x ∈ xs, Typed x
  | [], _ => by simp
  | _ :: _, h => by simp [AppShape.toEo, Arity.accepts] at h; exact absurd h typed_stuck

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

theorem spineAtLeast {head : Term} {n : Nat}
    (hlem : ∀ xs : List Term, Typed (xs.foldl Term.Apply head) → ∀ x ∈ xs, Typed x) :
    ∀ xs : List Term, Typed ((AppShape.spine head (.atLeast n)).toEo xs) → ∀ x ∈ xs, Typed x := by
  intro xs h
  simp only [AppShape.toEo] at h
  split at h
  · exact hlem xs h
  · exact absurd h typed_stuck

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

theorem none_shape : ∀ xs : List Term, Typed (AppShape.none.toEo xs) → ∀ x ∈ xs, Typed x := by
  intro xs h; exact absurd h typed_stuck

variable [LogosFacts]

set_option hygiene false in
/-- The children of a binary application, by `typedN` or a special case. -/
macro "typed2s" : tactic => `(tactic| first | typedN | exact typed_select x y h | exact typed_set_member x y h | exact LogosFacts.tuple_args x y h)

set_option hygiene false in
/-- The children of a ternary application, by `typedN` or a special case. -/
macro "typed3s" : tactic => `(tactic| first | typedN | exact typed_store x y z h | exact typed_ite x y z h | exact typed_bvite x y z h)

/-- Children of the applications of an operator kind. -/
theorem kind_children {k : Kind} (hc : (Op.kind k).childrenTypedOfParent = true) :
    ∀ xs : List Term, Typed (k.eoShape.toEo xs) → ∀ x ∈ xs, Typed x := by
  cases k <;> simp only [Op.childrenTypedOfParent, Kind.eoShape, Bool.false_eq_true] at hc <;>
    try simp only [Kind.eoShape]
  all_goals first
    | exact none_shape
    | exact distinct_children
    | exact spine0
    | exact spine1 (fun x h => by typed1)
    | exact spine2 (fun x y h => by typed2s)
    | exact spine3 (fun x y z h => by typed3s)
    | exact rassoc (fun x y h => by typedN)

/-- Children of the applications of an indexed operator. -/
theorem indexed_children (k : Kind) (is : List Int) :
    ∀ xs : List Term, Typed ((indexedEoShape k is).toEo xs) → ∀ x ∈ xs, Typed x := by
  unfold indexedEoShape
  split
  all_goals first
    | exact none_shape
    | exact spine1 (fun x h => LogosFacts.uop1_arg _ _ x h)
    | exact spine1 (fun x h => by typed1)
    | exact spine2 (fun x y h => LogosFacts.update_args _ _ x y (.inl rfl) h)

/-- **Children of a well-typed application are well typed**, for the operators
of `Op.childrenTypedOfParent`. -/
theorem children_wellTyped {op : Op} {cs : Array Node} (hc : op.childrenTypedOfParent = true)
    (h : (Node.app op cs).WellTyped) : ∀ c ∈ cs.toList, c.WellTyped := by
  have h' : Typed (op.eoShape.toEo (cs.toList.map Node.toEo)) := by
    rw [← Node.toEo_app]; exact h
  suffices hs : ∀ x ∈ cs.toList.map Node.toEo, Typed x by
    intro c hcm; exact hs _ (List.mem_map_of_mem hcm)
  generalize cs.toList.map Node.toEo = xs at h' ⊢
  match op, hc with
  | .kind k, hc => exact kind_children hc xs h'
  | .indexed k is, _ => exact indexed_children k is.toList xs h'
  | .node .APPLY_UF (.var _ _), _ =>
    simp only [Op.eoShape, nodeEoShape, Node.toEo] at h'
    exact spineAtLeast (fun xs h => LogosFacts.uf_args _ _ xs h) xs h'
  | .node .APPLY_CONSTRUCTOR (.const (.dtCons (.datatype _ _) _)), _ =>
    simp only [Op.eoShape, nodeEoShape, Node.toEo, Const.toEo] at h'
    exact spineAtLeast (fun xs h => LogosFacts.dt_cons_args _ _ _ xs h) xs h'
  | .node .APPLY_SELECTOR (.const (.dtSel (.datatype _ _) _ _)), _ =>
    simp only [Op.eoShape, nodeEoShape, Node.toEo, Const.toEo] at h'
    exact spine1 (fun x h => LogosFacts.dt_sel_arg _ _ _ _ x h) xs h'
  | .node .APPLY_TESTER _, _ => exact spine1 (fun x h => LogosFacts.uop1_arg _ _ x h) xs h'
  | .node .APPLY_UPDATER _, _ =>
    exact spine2 (fun x y h => LogosFacts.update_args _ _ x y (.inr rfl) h) xs h'

end Telos.ChildTyping
