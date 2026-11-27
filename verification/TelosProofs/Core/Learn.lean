import TelosProofs.Core.Tri
import Telos.Core.Learn
import TelosProofs.Core.StrSplit

/-!
# Learned literals are implied

`SemProc.learn` (`Telos/Core/Learn.lean`): under `LearnPlan.Ok n m`, `n` is
equivalent to `m`, the conjunction `n` with the learned literals added
(`learn_equiv`), or `false` after a conflict (`conflict_equiv`). With the case of `reorg` (`Semantic.lean`), this gives
`SemProc.equiv`.

1. *Skeleton.* Every skeleton node is well typed: a conjunct of `n`, or a child
   of a well-typed Boolean connective (`ChildTyping.children_wellTyped`).
2. *One connective.* If the values `A` are of Boolean nodes, and hold in a
   model, the three-valued value of a well-typed connective (`eval3`) is, when
   it is defined, the value of the connective in the model (`eval3_sound`).
3. *The trace.* Item by item, the node of each item is Boolean, and in every
   model of `n` has the item's value (`replay_inv`). For `bwd p`: if the node
   had the other value, the values with it would hold, so the node of `p`
   would have the opposite of its value.
4. *The step.* So the added literals are Boolean, and true in every model of
   `n`, and `m` has the value of `n`. In a conflict, the last item and the
   values before it give its node both values in a model of `n`, so `n` has
   none, and is `false` (`conflict_equiv`).
-/

open Eo Smtm SmtEval

set_option linter.internalConstructors false

namespace Telos

set_option linter.unusedSectionVars false

variable [LogosFacts]

/-! ## Values -/

/-- The node has type `Bool`. -/
abbrev BoolT (t : Node) : Prop := t.smtType = SmtType.Bool

/-- The node has the value `b` in `M`. -/
abbrev EvalsTo (M : SmtModel) (t : Node) (b : Bool) : Prop :=
  __smtx_model_eval M t.toSmt = SmtValue.Boolean b

/-- The nodes given values are Boolean. -/
def ATyped (A : Assign) : Prop := ∀ k b, A.get? k = some b → BoolT k.node

/-- The values hold in `M`. -/
def AHolds (M : SmtModel) (A : Assign) : Prop := ∀ k b, A.get? k = some b → EvalsTo M k.node b

omit [LogosFacts] in
theorem boolT_const (b : Bool) : BoolT (.const (.boolean b)) := by
  cases b
  · simp [BoolT, Node.smtType, Node.toSmt, Node.toEo, Const.toEo]; exact typeof_false
  · simp [BoolT, Node.smtType, Node.toSmt, Node.toEo, Const.toEo]; exact typeof_true

omit [LogosFacts] in
theorem evalsTo_const (M : SmtModel) (b : Bool) : EvalsTo M (.const (.boolean b)) b := by
  cases b
  · simp [EvalsTo, Node.toSmt, Node.toEo, Const.toEo]; exact eval_false M
  · simp [EvalsTo, Node.toSmt, Node.toEo, Const.toEo]; exact eval_true M

omit [LogosFacts] in
theorem val_typed {A : Assign} (hA : ATyped A) {c : Node} {b : Bool} (h : A.val c = some b) :
    BoolT c := by
  unfold Assign.val at h
  split at h
  · exact boolT_const _
  · exact hA ⟨c⟩ b h

omit [LogosFacts] in
theorem val_holds {M : SmtModel} {A : Assign} (hA : AHolds M A) {c : Node} {b : Bool}
    (h : A.val c = some b) : EvalsTo M c b := by
  unfold Assign.val at h
  split at h
  · cases h; exact evalsTo_const M _
  · exact hA ⟨c⟩ b h

omit [LogosFacts] in
theorem get?_insert (A : Assign) (x : Node) (v : Bool) (k : Key) :
    (A.insert ⟨x⟩ v).get? k = if x = k.node then some v else A.get? k := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hx : x = k.node <;> simp [BEq.beq, hx]

omit [LogosFacts] in
theorem aTyped_insert {A : Assign} (hA : ATyped A) {x : Node} {v : Bool} (hx : BoolT x) :
    ATyped (A.insert ⟨x⟩ v) := by
  intro k b h
  rw [get?_insert] at h
  split at h
  · rename_i e; rw [← e]; exact hx
  · exact hA k b h

omit [LogosFacts] in
theorem aHolds_insert {M : SmtModel} {A : Assign} (hA : AHolds M A) {x : Node} {v : Bool}
    (hx : EvalsTo M x v) : AHolds M (A.insert ⟨x⟩ v) := by
  intro k b h
  rw [get?_insert] at h
  split at h
  · rename_i e; cases h; rw [← e]; exact hx
  · exact hA k b h

omit [LogosFacts] in
theorem aTyped_empty : ATyped ({} : Assign) := by
  intro k b h; simp at h

omit [LogosFacts] in
theorem aHolds_empty (M : SmtModel) : AHolds M ({} : Assign) := by
  intro k b h; simp at h

theorem evalsTo_of_bool {M : SmtModel} (hM : model_wf M) {t : Node} (h : BoolT t) :
    ∃ b, EvalsTo M t b :=
  LogosFacts.eval_bool M _ hM h

omit [LogosFacts] in
theorem evalsTo_unique {M : SmtModel} {t : Node} {a b : Bool} (ha : EvalsTo M t a)
    (hb : EvalsTo M t b) : a = b := by
  unfold EvalsTo at ha hb; rw [ha] at hb; simpa using hb

/-! ## Disjunctions -/

/-- The CPC disjunction of a list, ending in `false`. -/
abbrev orChain (xs : List Term) : Term := eoRightAssocNil UserOp.or (Term.Boolean false) xs

omit [LogosFacts] in
theorem toSmt_orChain_cons (x : Term) (xs : List Term) :
    __eo_to_smt (orChain (x :: xs)) = SmtTerm.or (__eo_to_smt x) (__eo_to_smt (orChain xs)) := rfl

omit [LogosFacts] in
theorem toSmt_orChain_nil : __eo_to_smt (orChain []) = SmtTerm.Boolean false := rfl

omit [LogosFacts] in
theorem typeof_or_bool (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.or a b) = SmtType.Bool ↔
      __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]
  simp only [native_ite, native_Teq]
  by_cases ha : __smtx_typeof a = SmtType.Bool <;> by_cases hb : __smtx_typeof b = SmtType.Bool <;>
    simp [ha, hb]

omit [LogosFacts] in
theorem eval_or (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.or a b) =
      __smtx_model_eval_or (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem typeof_orChain (xs : List Term) :
    __smtx_typeof (__eo_to_smt (orChain xs)) = SmtType.Bool ↔
      ∀ x ∈ xs, __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
  induction xs with
  | nil => simp [toSmt_orChain_nil, typeof_false]
  | cons x xs ih => rw [toSmt_orChain_cons, typeof_or_bool, ih]; simp

/-- A `Bool` disjunction chain is false iff its elements are. -/
theorem eval_orChain (M : SmtModel) (hM : model_wf M) (xs : List Term)
    (h : ∀ x ∈ xs, __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __smtx_model_eval M (__eo_to_smt (orChain xs)) = SmtValue.Boolean false ↔
      ∀ x ∈ xs, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean false := by
  induction xs with
  | nil => simp [toSmt_orChain_nil, eval_false]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih := ih fun y hy => h y (by simp [hy])
    obtain ⟨b, hb⟩ := LogosFacts.eval_bool M _ hM hx
    obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM ((typeof_orChain xs).2 fun y hy => h y (by simp [hy]))
    rw [toSmt_orChain_cons, eval_or, hb, hc]
    have ih' : c = false ↔ ∀ y ∈ xs, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean false := by
      rw [← ih, hc]; simp
    simp only [__smtx_model_eval_or, native_or, SmtValue.Boolean.injEq, Bool.or_eq_false_iff,
      List.mem_cons, forall_eq_or_imp, hb, ← ih']

omit [LogosFacts] in
theorem toEo_or (cs : Array Node) (h : 2 ≤ cs.size) :
    (Node.app (.kind .OR) cs).toEo = orChain (cs.toList.map Node.toEo) := by
  rw [Node.toEo_app]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval, h]

/-! ## Connectives -/

/-- A well-typed `and` or `or` has at least two children. -/
theorem nary_size {k : Kind} (hk : k = .AND ∨ k = .OR) {cs : Array Node}
    (h : (Node.app (.kind k) cs).WellTyped) : 2 ≤ cs.size := by
  by_contra hsz
  apply not_translation_stuck
  unfold Node.WellTyped Node.smtType Node.toSmt at h
  rw [Node.toEo_app] at h
  rcases hk with rfl | rfl <;>
    simpa [HasSmtType, Op.eoShape, Kind.eoShape, AppShape.toEo, hsz] using h

omit [LogosFacts] in
theorem mem_list_map {cs : Array Node} {P : Term → Prop}
    (h : ∀ i (hi : i < cs.size), P cs[i].toEo) : ∀ x ∈ cs.toList.map Node.toEo, P x := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  simpa using h i (by simpa using hi)

omit [LogosFacts] in
theorem all_of_list_map {cs : Array Node} {P : Term → Prop}
    (h : ∀ x ∈ cs.toList.map Node.toEo, P x) : ∀ i (hi : i < cs.size), P cs[i].toEo :=
  fun _ hi => h _ (List.mem_map_of_mem (Array.getElem_mem_toList hi))

omit [LogosFacts] in
theorem toSmt_spine1 (op : UserOp) (k : Kind) (hk : k.eoShape = .spine (Term.UOp op) (.exactly 1))
    (a : Node) : (Node.app (.kind k) #[a]).toEo = Term.Apply (Term.UOp op) a.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
theorem toEo_spine2 (op : UserOp) (k : Kind) (hk : k.eoShape = .spine (Term.UOp op) (.exactly 2))
    (a b : Node) :
    (Node.app (.kind k) #[a, b]).toEo = Term.Apply (Term.Apply (Term.UOp op) a.toEo) b.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
theorem toEo_ite (c t e : Node) :
    (Node.app (.kind .ITE) #[c, t, e]).toEo =
      Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c.toEo) t.toEo) e.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
theorem typeof_bin_bool (ty : SmtType) (a b : SmtTerm)
    (h : ty = native_ite (native_Teq (__smtx_typeof a) SmtType.Bool)
      (native_ite (native_Teq (__smtx_typeof b) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
    (hn : ty ≠ SmtType.None) :
    ty = SmtType.Bool ∧ __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  subst h
  simp only [native_ite, native_Teq] at *
  by_cases ha : __smtx_typeof a = SmtType.Bool <;> by_cases hb : __smtx_typeof b = SmtType.Bool <;>
    simp_all

omit [LogosFacts] in
theorem toList_one {cs : Array Node} (h : cs.size = 1) : cs.toList = [cs[0]] := by
  rcases cs with ⟨l⟩; match l, h with | [_], _ => rfl

omit [LogosFacts] in
theorem toList_two {cs : Array Node} (h : cs.size = 2) : cs.toList = [cs[0], cs[1]] := by
  rcases cs with ⟨l⟩; match l, h with | [_, _], _ => rfl

omit [LogosFacts] in
theorem toList_three {cs : Array Node} (h : cs.size = 3) : cs.toList = [cs[0], cs[1], cs[2]] := by
  rcases cs with ⟨l⟩; match l, h with | [_, _, _], _ => rfl

omit [LogosFacts] in
theorem toSmt_not {cs : Array Node} (h : cs.size = 1) :
    (Node.app (.kind .NOT) cs).toSmt = SmtTerm.not cs[0].toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_one h]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]
  rfl

omit [LogosFacts] in
theorem toSmt_eq {cs : Array Node} (h : cs.size = 2) :
    (Node.app (.kind .EQUAL) cs).toSmt = SmtTerm.eq cs[0].toSmt cs[1].toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_two h]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]
  rfl

omit [LogosFacts] in
theorem toSmt_xor {cs : Array Node} (h : cs.size = 2) :
    (Node.app (.kind .XOR) cs).toSmt = SmtTerm.xor cs[0].toSmt cs[1].toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_two h]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]
  rfl

omit [LogosFacts] in
theorem toSmt_imp {cs : Array Node} (h : cs.size = 2) :
    (Node.app (.kind .IMPLIES) cs).toSmt = SmtTerm.imp cs[0].toSmt cs[1].toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_two h]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]
  rfl

omit [LogosFacts] in
theorem toSmt_ite {cs : Array Node} (h : cs.size = 3) :
    (Node.app (.kind .ITE) cs).toSmt = SmtTerm.ite cs[0].toSmt cs[1].toSmt cs[2].toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_three h]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]
  rfl

omit [LogosFacts] in
theorem typeof_not' (a : SmtTerm) :
    __smtx_typeof (SmtTerm.not a) =
      native_ite (native_Teq (__smtx_typeof a) SmtType.Bool) SmtType.Bool SmtType.None := by
  rw [__smtx_typeof.eq_def]

omit [LogosFacts] in
theorem typeof_xor' (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.xor a b) = native_ite (native_Teq (__smtx_typeof a) SmtType.Bool)
      (native_ite (native_Teq (__smtx_typeof b) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None := by
  rw [__smtx_typeof.eq_def]

omit [LogosFacts] in
theorem typeof_imp' (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.imp a b) = native_ite (native_Teq (__smtx_typeof a) SmtType.Bool)
      (native_ite (native_Teq (__smtx_typeof b) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None := by
  rw [__smtx_typeof.eq_def]

omit [LogosFacts] in
theorem typeof_ite' (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.ite a b c) =
      __smtx_typeof_ite (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c) := by
  rw [__smtx_typeof.eq_def]

omit [LogosFacts] in
theorem typeof_ite_ok {T U V : SmtType} (h : __smtx_typeof_ite T U V ≠ SmtType.None) :
    T = SmtType.Bool ∧ U = V ∧ __smtx_typeof_ite T U V = U := by
  cases T <;> simp [__smtx_typeof_ite, native_ite, native_Teq] at h ⊢
  by_cases e : U = V <;> simp_all

omit [LogosFacts] in
theorem eval_not' (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not a) = __smtx_model_eval_not (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem eval_xor' (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.xor a b) =
      __smtx_model_eval_xor (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem eval_imp' (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.imp a b) =
      __smtx_model_eval_imp (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem eval_ite' (M : SmtModel) (a b c : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ite a b c) = __smtx_model_eval_ite (__smtx_model_eval M a)
      (__smtx_model_eval M b) (__smtx_model_eval M c) := by
  rw [__smtx_model_eval.eq_def]

/-! ## Conjunctions and disjunctions of arrays -/

omit [LogosFacts] in
theorem typeof_or_cases (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.or a b) = SmtType.Bool ∨ __smtx_typeof (SmtTerm.or a b) = SmtType.None := by
  rw [__smtx_typeof.eq_def]
  simp only [native_ite, native_Teq]
  by_cases ha : __smtx_typeof a = SmtType.Bool <;> by_cases hb : __smtx_typeof b = SmtType.Bool <;>
    simp [ha, hb]

omit [LogosFacts] in
theorem or_bool_iff (cs : Array Node) (h : 2 ≤ cs.size) :
    HasBoolType (Node.app (.kind .OR) cs).toEo ↔ ∀ i (hi : i < cs.size), HasBoolType cs[i].toEo := by
  rw [toEo_or cs h]
  unfold HasBoolType
  rw [typeof_orChain]
  exact ⟨fun hall => all_of_list_map hall, fun hall => mem_list_map hall⟩

omit [LogosFacts] in
theorem or_smtType_bool (cs : Array Node) (h : (Node.app (.kind .OR) cs).WellTyped) (hsz : 2 ≤ cs.size) :
    (Node.app (.kind .OR) cs).smtType = SmtType.Bool := by
  unfold Node.WellTyped Node.smtType Node.toSmt at *
  rw [toEo_or cs hsz] at *
  cases hcs : cs.toList.map Node.toEo with
  | nil =>
    have := congrArg List.length hcs
    rw [List.length_map, Array.length_toList, List.length_nil] at this
    omega
  | cons x xs =>
    rw [hcs, toSmt_orChain_cons] at h
    rw [toSmt_orChain_cons]
    exact (typeof_or_cases _ _).resolve_right h

theorem or_false_iff (cs : Array Node) (h : 2 ≤ cs.size) (M : SmtModel) (hM : model_wf M)
    (hb : ∀ i (hi : i < cs.size), HasBoolType cs[i].toEo) :
    EvalsTo M (Node.app (.kind .OR) cs) false ↔ ∀ i (hi : i < cs.size), EvalsTo M cs[i] false := by
  unfold EvalsTo Node.toSmt
  rw [toEo_or cs h, eval_orChain M hM _ (mem_list_map hb)]
  exact ⟨fun hall => all_of_list_map (P := fun t => __smtx_model_eval M (__eo_to_smt t) = _) hall,
    fun hall => mem_list_map (P := fun t => __smtx_model_eval M (__eo_to_smt t) = _) hall⟩

/-! ## One connective -/

/-- What `eval3_sound` proves of a connective. -/
abbrev Sound3 (A : Assign) (P : Node) (w : Bool) : Prop :=
  BoolT P ∧ ∀ M, model_wf M → AHolds M A → EvalsTo M P w

/-- A Boolean whose value is not `a` has value `!a`. -/
theorem evalsTo_two {M : SmtModel} (hM : model_wf M) {P : Node} (hP : BoolT P) {a : Bool}
    (h : ¬ EvalsTo M P a) : EvalsTo M P (!a) := by
  obtain ⟨c, hc⟩ := evalsTo_of_bool hM hP
  cases a <;> cases c
  all_goals first | exact absurd hc h | exact hc

theorem sound_and {A : Assign} {cs : Array Node} (hP : (Node.app (.kind .AND) cs).WellTyped)
    {w : Bool} (h : (if cs.any (fun c => A.val c == some false) then some false
      else if cs.all (fun c => A.val c == some true) then some true else none) = some w) :
    Sound3 A (.app (.kind .AND) cs) w := by
  have h2 := nary_size (Or.inl rfl) hP
  have hPb := and_smtType_bool cs hP
  have hb := (and_bool_iff cs h2).1 hPb
  refine ⟨hPb, fun M hM hH => ?_⟩
  have htrue := and_true_iff cs h2 M hM hb
  split at h
  · rename_i hany
    cases h
    obtain ⟨i, hi, hv⟩ := Array.any_eq_true.1 hany
    have hf : EvalsTo M cs[i] false := val_holds hH (by simpa using hv)
    refine evalsTo_two hM hPb (a := true) fun ht => ?_
    have := evalsTo_unique hf ((htrue.1 ht) i hi)
    simp at this
  · split at h
    · rename_i _ hall
      cases h
      refine htrue.2 fun i hi => ?_
      exact val_holds hH (by simpa using Array.all_eq_true.1 hall i hi)
    · simp at h

theorem sound_or {A : Assign} {cs : Array Node} (hP : (Node.app (.kind .OR) cs).WellTyped)
    {w : Bool} (h : (if cs.any (fun c => A.val c == some true) then some true
      else if cs.all (fun c => A.val c == some false) then some false else none) = some w) :
    Sound3 A (.app (.kind .OR) cs) w := by
  have h2 := nary_size (Or.inr rfl) hP
  have hPb := or_smtType_bool cs hP h2
  have hb := (or_bool_iff cs h2).1 hPb
  refine ⟨hPb, fun M hM hH => ?_⟩
  have hfalse := or_false_iff cs h2 M hM hb
  split at h
  · rename_i hany
    cases h
    obtain ⟨i, hi, hv⟩ := Array.any_eq_true.1 hany
    have ht : EvalsTo M cs[i] true := val_holds hH (by simpa using hv)
    refine evalsTo_two hM hPb (a := false) fun hf => ?_
    have := evalsTo_unique ht ((hfalse.1 hf) i hi)
    simp at this
  · split at h
    · rename_i _ hall
      cases h
      refine hfalse.2 fun i hi => ?_
      exact val_holds hH (by simpa using Array.all_eq_true.1 hall i hi)
    · simp at h

theorem sound_not {A : Assign} (hT : ATyped A) {cs : Array Node} {w : Bool}
    (h : (if h : cs.size = 1 then (A.val cs[0]).map (!·) else none) = some w) :
    Sound3 A (.app (.kind .NOT) cs) w := by
  split at h
  · rename_i hs
    cases hv : A.val cs[0] with
    | none => simp [hv] at h
    | some a =>
      simp only [hv, Option.map_some, Option.some.injEq] at h
      subst h
      have hb := val_typed hT hv
      refine ⟨?_, fun M _ hH => ?_⟩
      · unfold BoolT Node.smtType; rw [toSmt_not hs, typeof_not']
        unfold BoolT Node.smtType at hb; simp [native_ite, native_Teq, hb]
      · have := val_holds hH hv
        unfold EvalsTo at this ⊢
        rw [toSmt_not hs, eval_not', this]
        simp [__smtx_model_eval_not, native_not]
  · simp at h

theorem sound_ite {A : Assign} (hT : ATyped A) {cs : Array Node}
    (hP : (Node.app (.kind .ITE) cs).WellTyped) {w : Bool}
    (h : (if h : cs.size = 3 then
      match A.val cs[0] with
      | some true => A.val cs[1]
      | some false => A.val cs[2]
      | none =>
        match A.val cs[1], A.val cs[2] with
        | some a, some b => if a == b then some a else none
        | _, _ => none
    else none) = some w) :
    Sound3 A (.app (.kind .ITE) cs) w := by
  split at h
  · rename_i hs
    have hty := hP
    unfold Node.WellTyped Node.smtType at hty
    rw [toSmt_ite hs, typeof_ite'] at hty
    obtain ⟨hc, hte, hres⟩ := typeof_ite_ok hty
    have hPT : (Node.app (.kind .ITE) cs).smtType = cs[1].smtType := by
      unfold Node.smtType; rw [toSmt_ite hs, typeof_ite', hres]
    have hev : ∀ M, __smtx_model_eval M (Node.app (.kind .ITE) cs).toSmt =
        __smtx_model_eval_ite (__smtx_model_eval M cs[0].toSmt) (__smtx_model_eval M cs[1].toSmt)
          (__smtx_model_eval M cs[2].toSmt) := fun M => by rw [toSmt_ite hs, eval_ite']
    split at h
    · rename_i hv
      have hb1 := val_typed hT h
      refine ⟨hPT.trans hb1, fun M _ hH => ?_⟩
      unfold EvalsTo; rw [hev, val_holds hH hv, val_holds hH h]; try rfl
    · rename_i hv
      have hb2 := val_typed hT h
      refine ⟨hPT.trans (hte.trans hb2), fun M _ hH => ?_⟩
      unfold EvalsTo; rw [hev, val_holds hH hv, val_holds hH h]; try rfl
    · split at h
      · rename_i a b h1 h2
        split at h
        · rename_i hab
          simp only [beq_iff_eq] at hab
          subst hab
          cases h
          have hb1 := val_typed hT h1
          refine ⟨hPT.trans hb1, fun M hM hH => ?_⟩
          obtain ⟨c, hcv⟩ := evalsTo_of_bool hM hc
          unfold EvalsTo at hcv ⊢
          rw [hev, hcv, val_holds hH h1, val_holds hH h2]
          cases c <;> rfl
        · simp at h
      · simp at h
  · simp at h

theorem sound_eq {A : Assign} (hT : ATyped A) {cs : Array Node} {w : Bool}
    (h : (if h : cs.size = 2 then
      if cs[0] == cs[1] then none else
      match A.val cs[0], A.val cs[1] with
      | some a, some b => some (a == b)
      | _, _ => none
    else none) = some w) :
    Sound3 A (.app (.kind .EQUAL) cs) w := by
  split at h
  · rename_i hs
    split at h
    · simp at h
    · split at h
      · rename_i a b h1 h2
        cases h
        have hb1 := val_typed hT h1
        have hb2 := val_typed hT h2
        unfold BoolT Node.smtType at hb1 hb2
        refine ⟨?_, fun M _ hH => ?_⟩
        · unfold BoolT Node.smtType; rw [toSmt_eq hs, typeof_eq_eq, hb1, hb2]
          exact (typeof_eq_eq_bool_iff _ _).2 ⟨by simp, rfl⟩
        · unfold EvalsTo
          rw [toSmt_eq hs, model_eval_eq_eq, val_holds hH h1, val_holds hH h2]
          cases a <;> cases b <;> simp [__smtx_model_eval_eq, native_veq]
      · simp at h
  · simp at h

theorem sound_xor {A : Assign} (hT : ATyped A) {cs : Array Node} {w : Bool}
    (h : (if h : cs.size = 2 then
      if cs[0] == cs[1] then none else
      match A.val cs[0], A.val cs[1] with
      | some a, some b => some (a != b)
      | _, _ => none
    else none) = some w) :
    Sound3 A (.app (.kind .XOR) cs) w := by
  split at h
  · rename_i hs
    split at h
    · simp at h
    · split at h
      · rename_i a b h1 h2
        cases h
        have hb1 := val_typed hT h1
        have hb2 := val_typed hT h2
        unfold BoolT Node.smtType at hb1 hb2
        refine ⟨?_, fun M _ hH => ?_⟩
        · unfold BoolT Node.smtType; rw [toSmt_xor hs, typeof_xor', hb1, hb2]; simp [native_ite, native_Teq]
        · unfold EvalsTo
          rw [toSmt_xor hs, eval_xor', val_holds hH h1, val_holds hH h2]
          cases a <;> cases b <;>
            simp [__smtx_model_eval_xor, __smtx_model_eval_eq, __smtx_model_eval_not, native_veq, native_not]
      · simp at h
  · simp at h

theorem sound_imp {A : Assign} {cs : Array Node} (hP : (Node.app (.kind .IMPLIES) cs).WellTyped)
    {w : Bool}
    (h : (if h : cs.size = 2 then
      match A.val cs[0], A.val cs[1] with
      | some false, _ => some true
      | _, some true => some true
      | some true, some false => some false
      | _, _ => none
    else none) = some w) :
    Sound3 A (.app (.kind .IMPLIES) cs) w := by
  split at h
  · rename_i hs
    have hty := hP
    unfold Node.WellTyped Node.smtType at hty
    rw [toSmt_imp hs, typeof_imp'] at hty
    obtain ⟨hres, hb1, hb2⟩ := typeof_bin_bool _ _ _ rfl hty
    refine ⟨by unfold BoolT Node.smtType; rw [toSmt_imp hs, typeof_imp']; exact hres, fun M hM hH => ?_⟩
    obtain ⟨a, ha⟩ := evalsTo_of_bool hM (t := cs[0]) hb1
    obtain ⟨b, hb⟩ := evalsTo_of_bool hM (t := cs[1]) hb2
    have hval : EvalsTo M (.app (.kind .IMPLIES) cs) (!a || b) := by
      unfold EvalsTo at ha hb ⊢
      rw [toSmt_imp hs, eval_imp', ha, hb]
      simp [__smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not, native_or, native_not]
    have hx : ∀ c, A.val cs[0] = some c → c = a := fun c hc => evalsTo_unique (val_holds hH hc) ha
    have hy : ∀ c, A.val cs[1] = some c → c = b := fun c hc => evalsTo_unique (val_holds hH hc) hb
    suffices w = (!a || b) by rw [this]; exact hval
    split at h
    · rename_i h1; cases h; rw [← hx _ h1]; rfl
    · rename_i h2 _; cases h; rw [← hy _ h2]; simp
    · rename_i h1 h2; cases h; rw [← hx _ h1, ← hy _ h2]; rfl
    · simp at h
  · simp at h

/-- **One connective**: the three-valued value of a well-typed connective, from
Boolean values, is its value in every model where the values hold. -/
theorem eval3_sound {A : Assign} (hT : ATyped A) {P : Node} (hP : P.WellTyped) {w : Bool}
    (h : eval3 A P = some w) : Sound3 A P w := by
  unfold eval3 at h
  split at h
  · rename_i k cs
    unfold eval3K at h
    split at h
    · exact sound_and hP h
    · exact sound_or hP h
    · exact sound_not hT h
    · exact sound_ite hT hP h
    · exact sound_eq hT h
    · exact sound_xor hT h
    · exact sound_imp hP h
    · simp at h
  · simp at h

/-! ## Skeleton -/

omit [LogosFacts] in
theorem isBoolConn_children {P : Node} (h : isBoolConn P = true) :
    ∃ k cs, P = .app (.kind k) cs ∧ (Op.kind k).childrenTypedOfParent = true := by
  unfold isBoolConn at h
  split at h <;> first | exact ⟨_, _, rfl, rfl⟩ | simp at h

/-- **Skeleton nodes are well typed.** -/
theorem skel_wellTyped (L : LearnPlan) (cs : Array Node)
    (hcs : ∀ i (hi : i < cs.size), cs[i].WellTyped)
    (hS : ∀ s, s < L.skel.size → L.skelOk cs s = true) :
    ∀ s (hs : s < L.skel.size), L.skel[s].node.WellTyped := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro hs
  have h := hS s hs
  unfold LearnPlan.skelOk at h
  rw [Array.getElem?_eq_getElem hs] at h
  simp only at h
  split at h
  · simp only [beq_iff_eq] at h
    obtain ⟨hp, he⟩ := Array.getElem?_eq_some_iff.1 h
    rw [← he]; exact hcs _ hp
  · rename_i p _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hps, h⟩ := h
    rw [Array.getElem?_eq_getElem (by omega : p < L.skel.size)] at h
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hconn, hch⟩ := h
    have hPw := ih p hps (by omega)
    obtain ⟨k, ds, hk, hc⟩ := isBoolConn_children hconn
    rw [hk] at hPw hch
    obtain ⟨hpos, he⟩ := Array.getElem?_eq_some_iff.1 hch
    simp only [Node.getChildren] at hpos he
    rw [← he]
    exact ChildTyping.children_wellTyped hc hPw _ (Array.mem_toList_iff.2 (Array.getElem_mem hpos))

/-! ## Children forced backwards -/

omit [LogosFacts] in
theorem val_insert_ne (A : Assign) {x c : Node} (u : Bool) (h : x ≠ c) :
    Assign.val (A.insert ⟨x⟩ u) c = A.val c := by
  unfold Assign.val
  split
  · rfl
  · rw [get?_insert]; simp [h]

omit [LogosFacts] in
theorem boolT_wellTyped {t : Node} (h : BoolT t) : t.WellTyped := by
  unfold Node.WellTyped; unfold BoolT at h; rw [h]; simp

omit [LogosFacts] in
theorem mem_one {cs : Array Node} (h : cs.size = 1) {x : Node} (hx : x ∈ cs) : x = cs[0] := by
  have := Array.mem_toList_iff.2 hx; rw [toList_one h] at this; simpa using this

omit [LogosFacts] in
theorem mem_two {cs : Array Node} (h : cs.size = 2) {x : Node} (hx : x ∈ cs) :
    x = cs[0] ∨ x = cs[1] := by
  have := Array.mem_toList_iff.2 hx; rw [toList_two h] at this; simpa using this

omit [LogosFacts] in
theorem mem_three {cs : Array Node} (h : cs.size = 3) {x : Node} (hx : x ∈ cs) :
    x = cs[0] ∨ x = cs[1] ∨ x = cs[2] := by
  have := Array.mem_toList_iff.2 hx; rw [toList_three h] at this; simpa using this

omit [LogosFacts] in
theorem bin_children_bool {k : Kind} {cs : Array Node} (hs : cs.size = 2)
    (hsmt : (Node.app (.kind k) cs).toSmt = SmtTerm.xor cs[0].toSmt cs[1].toSmt ∨
      (Node.app (.kind k) cs).toSmt = SmtTerm.imp cs[0].toSmt cs[1].toSmt)
    (hP : BoolT (.app (.kind k) cs)) {x : Node} (hx : x ∈ cs) : BoolT x := by
  have hw := boolT_wellTyped hP
  unfold Node.WellTyped Node.smtType at hw
  have hb : BoolT cs[0] ∧ BoolT cs[1] := by
    rcases hsmt with e | e <;> rw [e] at hw
    · rw [typeof_xor'] at hw; exact (typeof_bin_bool _ _ _ rfl hw).2
    · rw [typeof_imp'] at hw; exact (typeof_bin_bool _ _ _ rfl hw).2
  rcases mem_two hs hx with rfl | rfl
  · exact hb.1
  · exact hb.2

omit [LogosFacts] in
theorem isBoolConn_kind {P : Node} (h : isBoolConn P = true) :
    ∃ k cs, P = .app (.kind k) cs ∧ (k = .AND ∨ k = .OR ∨ k = .NOT ∨ k = .ITE ∨ k = .EQUAL ∨
      k = .XOR ∨ k = .IMPLIES) := by
  unfold isBoolConn at h
  split at h <;> first | exact ⟨_, _, rfl, by simp⟩ | simp at h

/-- A child given a value backwards is Boolean. -/
theorem child_bool {A : Assign} (hT : ATyped A) {P x : Node} (hc : isBoolConn P = true)
    (hP : BoolT P) (hx : x ∈ P.getChildren) {u w : Bool} (h : eval3 (A.insert ⟨x⟩ u) P = some w) :
    BoolT x := by
  obtain ⟨k, cs, rfl, hk⟩ := isBoolConn_kind hc
  simp only [Node.getChildren] at hx
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h2 := nary_size (Or.inl rfl) (boolT_wellTyped hP)
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact (and_bool_iff cs h2).1 hP i hi
  · have h2 := nary_size (Or.inr rfl) (boolT_wellTyped hP)
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact (or_bool_iff cs h2).1 hP i hi
  · simp only [eval3, eval3K] at h
    split at h
    · rename_i hs
      rw [mem_one hs hx]
      unfold BoolT Node.smtType at hP ⊢
      rw [toSmt_not hs, typeof_not'] at hP
      simp only [native_ite, native_Teq] at hP
      by_cases e : __smtx_typeof cs[0].toSmt = SmtType.Bool
      · exact e
      · simp [e] at hP
    · simp at h
  · simp only [eval3, eval3K] at h
    split at h
    · rename_i hs
      have hw := boolT_wellTyped hP
      unfold Node.WellTyped Node.smtType at hw
      rw [toSmt_ite hs, typeof_ite'] at hw
      obtain ⟨hc0, hte, hres⟩ := typeof_ite_ok hw
      have h1 : BoolT cs[1] := by
        unfold BoolT Node.smtType at hP ⊢; rw [toSmt_ite hs, typeof_ite', hres] at hP; exact hP
      rcases mem_three hs hx with rfl | rfl | rfl
      · exact hc0
      · exact h1
      · exact hte.symm.trans h1
    · simp at h
  · simp only [eval3, eval3K] at h
    split at h
    · rename_i hs
      split at h
      · simp at h
      · rename_i hne
        simp only [beq_iff_eq] at hne
        split at h
        · rename_i a b h1 h2
          have heqt : cs[0].smtType = cs[1].smtType := by
            unfold BoolT Node.smtType at hP
            rw [toSmt_eq hs, typeof_eq_eq] at hP
            exact ((typeof_eq_eq_bool_iff _ _).1 hP).2
          have hb : BoolT cs[0] ∧ BoolT cs[1] := by
            by_cases hx0 : x = cs[0]
            · have hx1 : x ≠ cs[1] := hx0 ▸ hne
              rw [val_insert_ne A u hx1] at h2
              have := val_typed hT h2
              exact ⟨heqt.trans this, this⟩
            · rw [val_insert_ne A u hx0] at h1
              have := val_typed hT h1
              exact ⟨this, heqt.symm.trans this⟩
          rcases mem_two hs hx with rfl | rfl
          · exact hb.1
          · exact hb.2
        · simp at h
    · simp at h
  · simp only [eval3, eval3K] at h
    split at h
    · rename_i hs; exact bin_children_bool hs (Or.inl (toSmt_xor hs)) hP hx
    · simp at h
  · simp only [eval3, eval3K] at h
    split at h
    · rename_i hs; exact bin_children_bool hs (Or.inr (toSmt_imp hs)) hP hx
    · simp at h

/-! ## The trace -/

/-- After the first `k` items: the values are of Boolean nodes, the nodes of
the items are Boolean, and, in every model of the conjuncts `cs`, the values
hold and so do the items. -/
def TraceInv (L : LearnPlan) (cs : Array Node) (k : Nat) (A : Assign) : Prop :=
  ATyped A ∧ (∀ i (hi : i < L.trace.size), i < k → BoolT L.trace[i].node) ∧
  ∀ M, model_wf M → (∀ i (hi : i < cs.size), EvalsTo M cs[i] true) →
    AHolds M A ∧ ∀ i (hi : i < L.trace.size), i < k → EvalsTo M L.trace[i].node L.trace[i].value

/-- **One item.** -/
theorem item_sound (L : LearnPlan) (cs : Array Node)
    (hcb : ∀ i (hi : i < cs.size), BoolT cs[i])
    (hsk : ∀ s (hs : s < L.skel.size), L.skel[s].node.WellTyped)
    {k : Nat} (hk : k < L.trace.size) {A : Assign} (hI : TraceInv L cs k A)
    (h : L.itemOk cs A k L.trace[k] = true) :
    BoolT L.trace[k].node ∧ ∀ M, model_wf M → (∀ i (hi : i < cs.size), EvalsTo M cs[i] true) →
      EvalsTo M L.trace[k].node L.trace[k].value := by
  obtain ⟨hT, hTy, hH⟩ := hI
  unfold LearnPlan.itemOk at h
  split at h
  · rename_i pos _
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hv, hc⟩ := h
    obtain ⟨hp, he⟩ := Array.getElem?_eq_some_iff.1 hc
    rw [← he, hv]
    exact ⟨hcb pos hp, fun M _ hall => hall pos hp⟩
  · rename_i s _
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hs, h3⟩ := h
    cases hsk' : L.skel[s]? with
    | none => rw [hsk'] at hs; simp at hs
    | some sk =>
      rw [hsk'] at hs
      simp only [Option.map_some, Option.getD_some, beq_iff_eq] at hs
      obtain ⟨hsl, hse⟩ := Array.getElem?_eq_some_iff.1 hsk'
      have hw : L.trace[k].node.WellTyped := by rw [← hs, ← hse]; exact hsk s hsl
      obtain ⟨hb, hv⟩ := eval3_sound hT hw h3
      exact ⟨hb, fun M hM hall => hv M hM (hH M hM hall).1⟩
  · rename_i p _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hpk, h⟩ := h
    have hpl : p < L.trace.size := by omega
    rw [Array.getElem?_eq_getElem hpl] at h
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq,
      Array.contains_iff_mem] at h
    obtain ⟨⟨hconn, hmem⟩, h3⟩ := h
    have hPb := hTy p hpl hpk
    have hxb := child_bool hT hconn hPb hmem h3
    refine ⟨hxb, fun M hM hall => ?_⟩
    obtain ⟨hA, hitems⟩ := hH M hM hall
    have hPv := hitems p hpl hpk
    by_contra hne
    have hneg := evalsTo_two hM hxb hne
    have hT' := aTyped_insert hT (v := !L.trace[k].value) hxb
    have hA' := aHolds_insert hA hneg
    have := evalsTo_unique ((eval3_sound hT' (boolT_wellTyped hPb) h3).2 M hM hA') hPv
    cases hv : L.trace[p].value <;> simp [hv] at this

theorem traceInv_zero (L : LearnPlan) (cs : Array Node) : TraceInv L cs 0 {} :=
  ⟨aTyped_empty, fun _ _ h => absurd h (Nat.not_lt_zero _),
    fun M _ _ => ⟨aHolds_empty M, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem traceInv_step (L : LearnPlan) (cs : Array Node)
    (hcb : ∀ i (hi : i < cs.size), BoolT cs[i])
    (hsk : ∀ s (hs : s < L.skel.size), L.skel[s].node.WellTyped)
    {k : Nat} {A A' : Assign} (hI : TraceInv L cs k A) (h : L.replayStep cs A k = some A') :
    TraceInv L cs (k + 1) A' := by
  unfold LearnPlan.replayStep at h
  split at h
  · rename_i it hit
    obtain ⟨hk, rfl⟩ := Array.getElem?_eq_some_iff.1 hit
    split at h
    · rename_i hok
      cases h
      obtain ⟨hb, hv⟩ := item_sound L cs hcb hsk hk hI hok
      obtain ⟨hT, hTy, hH⟩ := hI
      refine ⟨aTyped_insert hT hb, fun i hi hik => ?_, fun M hM hall => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
        · exact hTy i hi hlt
        · exact hb
      · obtain ⟨hA, hitems⟩ := hH M hM hall
        refine ⟨aHolds_insert hA (hv M hM hall), fun i hi hik => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
        · exact hitems i hi hlt
        · exact hv M hM hall
    · simp at h
  · simp at h

/-- **The trace**: after replaying it, every item holds. -/
theorem replay_inv (L : LearnPlan) (cs : Array Node)
    (hcb : ∀ i (hi : i < cs.size), BoolT cs[i])
    (hsk : ∀ s (hs : s < L.skel.size), L.skel[s].node.WellTyped) :
    ∀ k {A : Assign}, (List.range k).foldlM (L.replayStep cs) {} = some A → TraceInv L cs k A := by
  intro k
  induction k with
  | zero => intro A h; simp at h; subst h; exact traceInv_zero L cs
  | succ k ih =>
    intro A h
    rw [List.range_succ, List.foldlM_append] at h
    cases h0 : (List.range k).foldlM (L.replayStep cs) {} with
    | none => rw [h0] at h; simp at h
    | some A₀ =>
      rw [h0] at h
      simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil] at h
      cases h1 : L.replayStep cs A₀ k with
      | none => rw [h1] at h; simp at h
      | some A₁ =>
        rw [h1] at h
        simp at h
        subst h
        exact traceInv_step L cs hcb hsk (ih h0) h1

/-! ## The step -/

omit [LogosFacts] in
theorem LearnPlan.ok_shape {L : LearnPlan} {n m : Node} (h : L.Ok n m = true) :
    ∃ cs, n = .app (.kind .AND) cs ∧
      (m = .const (.boolean false) ∨ ∃ ds, m = .app (.kind .AND) ds) := by
  unfold LearnPlan.Ok at h
  split at h
  · exact ⟨_, rfl, .inl rfl⟩
  · exact ⟨_, rfl, .inr ⟨_, rfl⟩⟩
  · simp at h

omit [LogosFacts] in
theorem boolT_litOf {it : LItem} (h : BoolT it.node) : BoolT (LearnPlan.litOf it) := by
  unfold LearnPlan.litOf
  split
  · exact h
  · unfold BoolT Node.smtType at h ⊢
    rw [toSmt_not (cs := #[it.node]) rfl, typeof_not']
    simp [native_ite, native_Teq, h]

omit [LogosFacts] in
theorem evalsTo_litOf {M : SmtModel} {it : LItem} (h : EvalsTo M it.node it.value) :
    EvalsTo M (LearnPlan.litOf it) true := by
  unfold LearnPlan.litOf
  split
  · rename_i hv; rw [hv] at h; exact h
  · rename_i hv
    simp only [Bool.not_eq_true] at hv
    rw [hv] at h
    unfold EvalsTo at h ⊢
    rw [toSmt_not (cs := #[it.node]) rfl, eval_not']
    simp only [List.getElem_toArray, List.getElem_cons_zero]
    rw [h]
    simp [__smtx_model_eval_not, native_not]

/-- **Learned literals are implied.** -/
theorem learn_equiv (L : LearnPlan) (cs ds : Array Node)
    (hok : L.Ok (.app (.kind .AND) cs) (.app (.kind .AND) ds) = true)
    (hn : (Node.app (.kind .AND) cs).WellTyped) :
    (Node.app (.kind .AND) cs).Equiv (.app (.kind .AND) ds) := by
  simp only [LearnPlan.Ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Option.isSome_iff_exists] at hok
  obtain ⟨⟨⟨⟨⟨h2, hsz⟩, hpre⟩, hlits⟩, hskel⟩, A, hrep⟩ := hok
  have h2' : 2 ≤ ds.size := by omega
  have hnb : HasBoolType (Node.app (.kind .AND) cs).toEo := and_smtType_bool cs hn
  have hcb : ∀ i (hi : i < cs.size), BoolT cs[i] := (and_bool_iff cs h2).1 hnb
  have hsk := skel_wellTyped L cs (fun i hi => boolT_wellTyped (hcb i hi)) hskel
  have hI := replay_inv L cs hcb hsk _ hrep
  obtain ⟨_, hTy, hH⟩ := hI
  -- the conjuncts of `ds`: those of `cs`, then the literals
  have hpre' : ∀ i (hi : i < cs.size), ds[i]'(by omega) = cs[i] := by
    intro i hi
    have := hpre i hi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hlit : ∀ j (hj : j < L.lits.size), ∃ t, ∃ ht : t < L.trace.size,
      ds[cs.size + j]'(by omega) = LearnPlan.litOf L.trace[t] := by
    intro j hj
    have := hlits j hj
    rw [Array.getElem?_eq_getElem hj] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨ht, h⟩ := this
    rw [Array.getElem?_eq_getElem ht] at h
    simp only [Option.map_some, Option.getD_some, beq_iff_eq] at h
    rw [Array.getElem?_eq_getElem (by omega)] at h
    exact ⟨_, ht, by simpa using h⟩
  have hds : ∀ i (hi : i < ds.size), BoolT ds[i] ∧
      ∀ M, model_wf M → (∀ i (hi : i < cs.size), EvalsTo M cs[i] true) → EvalsTo M ds[i] true := by
    intro i hi
    by_cases hic : i < cs.size
    · rw [hpre' i hic]; exact ⟨hcb i hic, fun M _ hall => hall i hic⟩
    · obtain ⟨t, ht, he⟩ := hlit (i - cs.size) (by omega)
      have e : ds[i] = ds[cs.size + (i - cs.size)]'(by omega) := by congr 1; omega
      rw [e, he]
      exact ⟨boolT_litOf (hTy t ht ht), fun M hM hall => evalsTo_litOf ((hH M hM hall).2 t ht ht)⟩
  have hmb : HasBoolType (Node.app (.kind .AND) ds).toEo := (and_bool_iff ds h2').2 fun i hi => (hds i hi).1
  refine (Node.equiv_iff _ _).2 ⟨hn, ?_, fun M hM => ?_⟩
  · exact hnb.trans hmb.symm
  · have hn' := and_true_iff cs h2 M hM hcb
    have hm' := and_true_iff ds h2' M hM fun i hi => (hds i hi).1
    obtain ⟨b, hb⟩ := LogosFacts.eval_bool M _ hM hnb
    obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hmb
    have hiff : b = true ↔ c = true := by
      unfold TrueIn at hn' hm'
      rw [hb] at hn'; rw [hc] at hm'
      simp only [SmtValue.Boolean.injEq] at hn' hm'
      rw [hn', hm']
      exact ⟨fun hall i hi => (hds i hi).2 M hM hall,
        fun hall i hi => by have := hall i (by omega); rwa [hpre' i hi] at this⟩
    have : b = c := by cases b <;> cases c <;> simp_all
    change SmtValueRel (__smtx_model_eval M (__eo_to_smt (Node.app (.kind .AND) cs).toEo))
      (__smtx_model_eval M (__eo_to_smt (Node.app (.kind .AND) ds).toEo))
    rw [hb, hc, this]
    exact LogosFacts.value_rel_refl _

/-- **A conflict**: no model of the conjuncts satisfies the trace, whose last
item contradicts the others, so the conjunction is `false`. -/
theorem conflict_equiv (L : LearnPlan) (cs : Array Node)
    (hok : L.Ok (.app (.kind .AND) cs) (.const (.boolean false)) = true)
    (hn : (Node.app (.kind .AND) cs).WellTyped) :
    (Node.app (.kind .AND) cs).Equiv (.const (.boolean false)) := by
  simp only [LearnPlan.Ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨h2, hskel⟩, hc⟩ := hok
  have hnb : HasBoolType (Node.app (.kind .AND) cs).toEo := and_smtType_bool cs hn
  have hcb : ∀ i (hi : i < cs.size), BoolT cs[i] := (and_bool_iff cs h2).1 hnb
  have hsk := skel_wellTyped L cs (fun i hi => boolT_wellTyped (hcb i hi)) hskel
  have hno : ∀ M, model_wf M → ¬ ∀ i (hi : i < cs.size), EvalsTo M cs[i] true := by
    intro M hM hall
    unfold LearnPlan.conflictOk at hc
    split at hc
    · simp at hc
    · rename_i k hk
      split at hc
      · rename_i A it hA hit
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hitem, hval⟩ := hc
        have hkl : k < L.trace.size := by omega
        obtain ⟨_, rfl⟩ := Array.getElem?_eq_some_iff.1 hit
        have hI := replay_inv L cs hcb hsk k hA
        have h₁ := (item_sound L cs hcb hsk hkl hI hitem).2 M hM hall
        have h₂ := val_holds (hI.2.2 M hM hall).1 hval
        have := evalsTo_unique h₁ h₂
        cases hb : L.trace[k].value <;> simp [hb] at this
      · simp at hc
  refine (Node.equiv_iff _ _).2 ⟨hn, hnb.trans (boolT_const false).symm, fun M hM => ?_⟩
  obtain ⟨b, hb⟩ := LogosFacts.eval_bool M _ hM hnb
  have hn' := and_true_iff cs h2 M hM hcb
  have hbf : b = false := by
    cases b
    · rfl
    · exfalso; apply hno M hM; unfold TrueIn at hn'; rw [hb] at hn'; exact hn'.1 rfl
  have hf := evalsTo_const M false
  unfold EvalsTo at hf
  change SmtValueRel (__smtx_model_eval M (__eo_to_smt (Node.app (.kind .AND) cs).toEo))
    (__smtx_model_eval M (__eo_to_smt (Node.const (.boolean false)).toEo))
  rw [hb, hbf]
  erw [hf]
  exact LogosFacts.value_rel_refl _

/-- **Semantically justified steps are equivalences.** -/
theorem SemProc.equiv : ∀ (p : SemProc) (n m : Node), p.Ok n m → n.WellTyped → n.Equiv m
  | .reorg, n, m, h, hn => SemProc.reorg_equiv n m h hn
  | .learn L, n, m, h, hn => by
    have h' : L.Ok n m = true := h
    obtain ⟨cs, rfl, hm⟩ := LearnPlan.ok_shape h'
    rcases hm with rfl | ⟨ds, rfl⟩
    · exact conflict_equiv L cs h' hn
    · exact learn_equiv L cs ds h' hn
  | .strSplit i j, n, m, h, hn => StrSplitProof.strSplit_equiv i j n m h hn

end Telos
