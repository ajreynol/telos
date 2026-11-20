import TelosProofs.Solver.Solve
import Telos.Solver.Model

/-!
# Models are sound

A model (`Telos/Solver/Model.lean`) is a substitution: values for the
constants, and tables for the functions. Its Logos model (`toSmtModel`)
interprets a constant by its value, a function by its tables, and every other
symbol by the default of its type. Each element of an uninterpreted sort is
the identifier of its number.

1. The Logos model is well formed (`toSmtModel_wf`), if the model's constants
   and tables are well typed (`constsOk`, `tablesOk`, which `satisfies`
   checks).
2. The evaluation is Logos's (`ev_sound`): if `Model.ev` gives a value, the
   Logos model evaluates the node's translation to that value.

So a model that satisfies the input assertions shows that they are
satisfiable (`satisfies_sound`).
-/

open Eo Smtm SmtEval

namespace Telos.Solver

set_option linter.unusedSectionVars false
set_option linter.internalConstructors false

variable [LogosFacts]

/-- The Logos value of a value. -/
noncomputable def toVal : MVal → SmtValue
  | .bool b => .Boolean b
  | .uval s i => .UValue s (i : ℝ)
  | .fn fid d r => .Fun ((fid : ℝ) + 1) d r

omit [LogosFacts] in
theorem toVal_inj {a b : MVal} (h : toVal a = toVal b) : a = b := by
  cases a <;> cases b <;> simp_all [toVal]

omit [LogosFacts] in
theorem typeof_toVal (v : MVal) : __smtx_typeof_value (toVal v) = v.ty := by
  cases v <;> simp [toVal, MVal.ty, __smtx_typeof_value]

/-- The function of a model's identifier. -/
noncomputable def tableFun (M : Model) (e : ModelId) (A B : SmtType) (i : SmtValue) : SmtValue :=
  open Classical in
  if h : ∃ k : ℕ, e = (k : ℝ) + 1 then
    match M.funs[Classical.choose h]? with
    | some t =>
      if t.dom = A ∧ t.rng = B then
        match t.entries.find? (fun p => decide (toVal p.1 = i)) with
        | some (_, v) => toVal v
        | none => toVal t.default
      else __smtx_type_default B
    | none => __smtx_type_default B
  else __smtx_type_default B

/-- **The Logos model of a model.** -/
noncomputable def toSmtModel (M : Model) : SmtModel where
  values k :=
    if k.isVar then __smtx_type_default k.ty else
    match M.consts.get? k.name with
    | some (T, v) => if T = k.ty then toVal v else __smtx_type_default k.ty
    | none => __smtx_type_default k.ty
  nativeFuns := tableFun M
  usortDom := fun _ => Set.univ

omit [LogosFacts] in
theorem usort_dom_wf_univ : usort_dom_wf (fun _ => (Set.univ : Set ModelId)) := by
  intro i
  refine ⟨Set.mem_univ _, fun _ n => ⟨(n : ℝ), Set.mem_univ _, ?_⟩⟩
  simp

omit [LogosFacts] in
theorem canonical_toVal (v : MVal) :
    __smtx_value_canonical (fun _ => (Set.univ : Set ModelId)) (toVal v) = true := by
  cases v <;> simp [toVal, __smtx_value_canonical, native_usort_mem]

theorem default_ok {T : SmtType} (h : __smtx_type_wf T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (fun _ => (Set.univ : Set ModelId)) (__smtx_type_default T) = true :=
  LogosFacts.type_default_ok _ usort_dom_wf_univ T h

omit [LogosFacts] in
theorem type_wf_range {A B : SmtType} (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf B = true := by
  simp only [__smtx_type_wf, native_and, Bool.and_eq_true] at h
  exact h.2

omit [LogosFacts] in
theorem constsOk_get {M : Model} (h : M.constsOk = true) {k : native_String} {T : SmtType} {v : MVal}
    (hk : M.consts.get? k = some (T, v)) : v.ty = T := by
  unfold Model.constsOk at h
  rw [List.all_eq_true] at h
  have hm : (k, (T, v)) ∈ M.consts.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.2 (by simpa using hk)
  simpa using h _ hm

omit [LogosFacts] in
theorem tablesOk_get {M : Model} (h : M.tablesOk = true) {k : Nat} {t : FunTable}
    (hk : M.funs[k]? = some t) :
    (∀ p ∈ t.entries, p.2.ty = t.rng) ∧ t.default.ty = t.rng := by
  unfold Model.tablesOk at h
  rw [Array.all_eq_true_iff_forall_mem] at h
  have := h t (Array.mem_of_getElem? hk)
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
  exact ⟨fun p hp => this.1 p hp, this.2⟩

/-- **The Logos model is well formed.** -/
theorem toSmtModel_wf {M : Model} (hc : M.constsOk = true) (ht : M.tablesOk = true) :
    model_wf (toSmtModel M) := by
  refine ⟨?_, ?_, ?_, usort_dom_wf_univ⟩
  · intro isVar s T hT
    simp only [toSmtModel]
    split
    · exact (default_ok hT).1
    · split
      · rename_i T' v hk
        split
        · rename_i hTT; subst hTT; rw [typeof_toVal]; exact constsOk_get hc hk
        · exact (default_ok hT).1
      · exact (default_ok hT).1
  · intro isVar s T hT
    simp only [toSmtModel]
    split
    · exact (default_ok hT).2
    · split
      · split
        · exact canonical_toVal _
        · exact (default_ok hT).2
      · exact (default_ok hT).2
  · intro fid A B i hAB _
    have hB := type_wf_range hAB
    unfold native_eval_fun_apply
    split
    · exact default_ok hB
    · simp only [model_fun_lookup, toSmtModel, tableFun]
      split
      · rename_i hfid
        split
        · rename_i t htk
          obtain ⟨hentries, hdef⟩ := tablesOk_get ht htk
          split
          · rename_i hty
            obtain ⟨-, rfl⟩ := hty
            split
            · rename_i a v hfind
              refine ⟨by rw [typeof_toVal]; exact hentries _ (List.mem_of_find?_eq_some hfind), ?_⟩
              exact canonical_toVal _
            · exact ⟨by rw [typeof_toVal]; exact hdef, canonical_toVal _⟩
          · exact default_ok hB
        · exact default_ok hB
      · exact default_ok hB

/-! ## Evaluation -/

/-- The memo has the values of its nodes in the model. -/
def MemoOk (M : Model) (S : Model.Memo) : Prop :=
  ∀ t v, S.get? ⟨t⟩ = some (some v) → __smtx_model_eval (toSmtModel M) t.toSmt = toVal v

omit [LogosFacts] in
theorem memoOk_empty (M : Model) : MemoOk M {} := by
  intro t v h; simp at h

omit [LogosFacts] in
theorem memoOk_insert {M : Model} {S : Model.Memo} (hS : MemoOk M S) {t : Node} {r : Option MVal}
    (ht : ∀ v, r = some v → __smtx_model_eval (toSmtModel M) t.toSmt = toVal v) : MemoOk M (S.insert ⟨t⟩ r) := by
  intro u v h
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    have htu : t = u := by simpa using heq
    subst htu
    exact ht v (Option.some.inj h)
  · exact hS u v (by simpa [Std.HashMap.get?_eq_getElem?] using h)

omit [LogosFacts] in
theorem toSmt_var (x : String) (T : TypeNode) :
    (Node.var x T).toSmt = SmtTerm.UConst (keyName x) (tyS T) := by
  unfold Node.toSmt; rw [Node.toEo]; rfl

omit [LogosFacts] in
theorem eval_var {M : Model} {x : String} {T : TypeNode} {v : MVal} (h : M.const x T = some v) :
    __smtx_model_eval (toSmtModel M) (Node.var x T).toSmt = toVal v := by
  unfold Model.const at h
  rw [toSmt_var, __smtx_model_eval.eq_def]
  simp only [native_model_lookup, model_key, toSmtModel]
  split at h
  · rename_i T' w hk
    split at h
    · rename_i hT
      cases h
      simp only [Bool.false_eq_true, ↓reduceIte, hk, beq_iff_eq.1 hT]
    · cases h
  · cases h

/-! ### Connectives -/

omit [LogosFacts] in
theorem eval_eq' (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) = __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem eval_eq_toVal (a b : MVal) :
    __smtx_model_eval_eq (toVal a) (toVal b) = SmtValue.Boolean (a == b) := by
  have e : __smtx_model_eval_eq (toVal a) (toVal b) = SmtValue.Boolean (native_veq (toVal a) (toVal b)) := by
    cases a <;> cases b <;> rfl
  rw [e]
  congr 1
  simp only [native_veq]
  by_cases h : a = b
  · subst h; simp
  · have : toVal a ≠ toVal b := fun e => h (toVal_inj e)
    simp [h, this]

/-- Each node has the value of its value in the model. -/
abbrev Vals (M : Model) (l : List Node) (vs : List MVal) : Prop :=
  List.Forall₂ (fun c v => __smtx_model_eval (toSmtModel M) c.toSmt = toVal v) l vs

omit [LogosFacts] in
theorem vals_map {M : Model} : ∀ {l : List Node} {vs : List MVal}, Vals M l vs →
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModel M) (__eo_to_smt x) = toVal v) (l.map Node.toEo) vs
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h (vals_map hr)

omit [LogosFacts] in
theorem eval_andChain_vals (M : Model) : ∀ (xs : List Term) (vs : List MVal) (bs : List Bool),
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModel M) (__eo_to_smt x) = toVal v) xs vs →
    Model.bools vs = some bs →
    __smtx_model_eval (toSmtModel M) (__eo_to_smt (andChain xs)) = SmtValue.Boolean (bs.all id)
  | [], [], bs, .nil, h => by
    simp only [Model.bools, Option.some.injEq] at h; subst h
    exact eval_true _
  | x :: xs, v :: vs, bs, .cons hx hr, h => by
    cases v with
    | bool b =>
      simp only [Model.bools] at h
      obtain ⟨bs', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [toSmt_andChain_cons, eval_and, hx, eval_andChain_vals M xs vs bs' hr hb']
      simp [toVal, __smtx_model_eval_and, native_and]
    | _ => simp [Model.bools] at h

omit [LogosFacts] in
theorem eval_orChain_vals (M : Model) : ∀ (xs : List Term) (vs : List MVal) (bs : List Bool),
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModel M) (__eo_to_smt x) = toVal v) xs vs →
    Model.bools vs = some bs →
    __smtx_model_eval (toSmtModel M) (__eo_to_smt (orChain xs)) = SmtValue.Boolean (bs.any id)
  | [], [], bs, .nil, h => by
    simp only [Model.bools, Option.some.injEq] at h; subst h
    exact eval_false _
  | x :: xs, v :: vs, bs, .cons hx hr, h => by
    cases v with
    | bool b =>
      simp only [Model.bools] at h
      obtain ⟨bs', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [toSmt_orChain_cons, eval_or, hx, eval_orChain_vals M xs vs bs' hr hb']
      simp [toVal, __smtx_model_eval_or, native_or]
    | _ => simp [Model.bools] at h

omit [LogosFacts] in
/-- **A connective has its value.** -/
theorem combine_sound (M : Model) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : Vals M cs.toList vs) (h : Model.combine k vs = some r) :
    __smtx_model_eval (toSmtModel M) (Node.app (.kind k) cs).toSmt = toVal r := by
  have hlen : cs.size = vs.length := by simpa using hv.length_eq
  unfold Model.combine at h
  split at h
  · rename_i b
    cases h
    have hs : cs.size = 1 := by simpa using hlen
    rw [toList_one hs] at hv
    rw [toSmt_not hs, eval_not', (List.forall₂_cons.1 hv).1]
    rfl
  · split at h
    · rename_i h2
      obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.1 h
      have hs : 2 ≤ cs.size := by omega
      unfold Node.toSmt
      rw [toEo_and cs hs]
      exact eval_andChain_vals M _ _ _ (vals_map hv) hbs
    · cases h
  · split at h
    · rename_i h2
      obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.1 h
      have hs : 2 ≤ cs.size := by omega
      unfold Node.toSmt
      rw [toEo_or cs hs]
      exact eval_orChain_vals M _ _ _ (vals_map hv) hbs
    · cases h
  · cases h
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_imp hs, eval_imp', h0, h1]
    simp [toVal, __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not, native_or, native_not]
  · rename_i a b
    cases h
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_xor hs, eval_xor', h0, h1]
    cases a <;> cases b <;>
      simp [toVal, __smtx_model_eval_xor, __smtx_model_eval_eq, __smtx_model_eval_not, native_veq, native_not]
  · cases h
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_eq hs, eval_eq', h0, h1, eval_eq_toVal]
    rfl
  · rename_i c a b
    cases h
    have hs : cs.size = 3 := by simpa using hlen
    rw [toList_three hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h2, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_ite hs, eval_ite', h0, h1, h2]
    cases c <;> simp [toVal, __smtx_model_eval_ite]
  · cases h

/-! ### `distinct` -/

/-- A CPC typed list. -/
abbrev tl (nl : Term) (xs : List Term) : Term := eoRightAssocNil UserOp._at__at_TypedList_cons nl xs

omit [LogosFacts] in
theorem elem_tail {x : Term} {xs : List Term} {nl : Term}
    (h : __eo_to_smt_typed_list_elem_type (tl nl (x :: xs)) ≠ SmtType.None) :
    __eo_to_smt_typed_list_elem_type (tl nl xs) ≠ SmtType.None := by
  intro h'
  apply h
  simp only [tl, eoRightAssocNil, eoApp2] at h' ⊢
  rw [__eo_to_smt_typed_list_elem_type.eq_def]
  simp only [h', native_ite, native_Teq]
  split <;> simp_all

omit [LogosFacts] in
theorem elem_nil {xs : List Term} {nl : Term}
    (h : __eo_to_smt_typed_list_elem_type (tl nl xs) ≠ SmtType.None) :
    __eo_to_smt_typed_list_elem_type nl ≠ SmtType.None := by
  induction xs with
  | nil => exact h
  | cons x xs ih => exact ih (elem_tail h)

omit [LogosFacts] in
theorem typedNil_cons (x : Term) :
    typedNil UserOp._at__at_TypedList_cons x = Term.Stuck ∨
      ∃ T, typedNil UserOp._at__at_TypedList_cons x = Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T := by
  unfold typedNil
  simp only [typedNilOfType]
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

omit [LogosFacts] in
theorem eval_pairs (M : Model) (T : Term) (s : SmtTerm) (sv : MVal)
    (hs : __smtx_model_eval (toSmtModel M) s = toVal sv) : ∀ (xs : List Term) (vs : List MVal),
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModel M) (__eo_to_smt x) = toVal v) xs vs →
    __smtx_model_eval (toSmtModel M)
        (__eo_to_smt_distinct_pairs s (tl (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) xs)) =
      SmtValue.Boolean (vs.all fun w => !(sv == w))
  | [], [], .nil => by
    simp only [tl, eoRightAssocNil, __eo_to_smt_distinct_pairs]
    exact eval_true _
  | x :: xs, v :: vs, .cons hx hr => by
    simp only [tl, eoRightAssocNil, eoApp2, __eo_to_smt_distinct_pairs]
    rw [eval_and, eval_not', eval_eq', hs, hx, eval_eq_toVal]
    have := eval_pairs M T s sv hs xs vs hr
    simp only [tl] at this
    rw [this]
    cases hb : (sv == v) <;> simp [hb, __smtx_model_eval_not, __smtx_model_eval_and, native_and, native_not]

omit [LogosFacts] in
theorem eval_distinct (M : Model) (T : Term) : ∀ (xs : List Term) (vs : List MVal),
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModel M) (__eo_to_smt x) = toVal v) xs vs →
    __smtx_model_eval (toSmtModel M)
        (__eo_to_smt_distinct (tl (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) xs)) =
      SmtValue.Boolean (Model.distinctVals vs)
  | [], [], .nil => by
    simp only [tl, eoRightAssocNil, __eo_to_smt_distinct]
    exact eval_true _
  | x :: xs, v :: vs, .cons hx hr => by
    simp only [tl, eoRightAssocNil, eoApp2, __eo_to_smt_distinct]
    have hp := eval_pairs M T _ v hx xs vs hr
    have hd := eval_distinct M T xs vs hr
    simp only [tl] at hp hd
    rw [eval_and, hp, hd]
    simp [Model.distinctVals, __smtx_model_eval_and, native_and]

omit [LogosFacts] in
/-- **A `distinct` has its value.** -/
theorem distinct_sound (M : Model) {cs : Array Node} {vs : List MVal}
    (hv : Vals M cs.toList vs) (hty : Model.distinctTyped cs = true) (h2 : 2 ≤ vs.length) :
    __smtx_model_eval (toSmtModel M) (Node.app (.kind .DISTINCT) cs).toSmt =
      toVal (.bool (Model.distinctVals vs)) := by
  have hs : 2 ≤ cs.size := by have := hv.length_eq; simp at this; omega
  have hte : (Node.app (.kind .DISTINCT) cs).toEo =
      Term.Apply (Term.UOp UserOp.distinct) (Model.distinctList cs) := by
    rw [Node.toEo_app]
    simp [Op.eoShape, Kind.eoShape, AppShape.toEo, hs, Model.distinctList, eoApp1]
  have hel : __eo_to_smt_typed_list_elem_type (Model.distinctList cs) ≠ SmtType.None := by
    simpa [Model.distinctTyped] using hty
  unfold Node.toSmt
  rw [hte]
  show __smtx_model_eval _ (native_ite (native_Teq (__eo_to_smt_typed_list_elem_type (Model.distinctList cs))
    SmtType.None) SmtTerm.None (__eo_to_smt_distinct (Model.distinctList cs))) = _
  simp only [native_ite, native_Teq, hel, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold Model.distinctList at hel ⊢
  have hnl := elem_nil hel
  rcases typedNil_cons ((cs.toList.map Node.toEo).headD Term.Stuck) with hn | ⟨T, hn⟩
  · rw [hn] at hnl
    exact absurd (by rw [__eo_to_smt_typed_list_elem_type.eq_def]) hnl
  · simp only [hn]
    exact eval_distinct M T _ _ (vals_map hv)

/-! ### Applications of declared functions -/

/-- A curried application of a constant. -/
inductive UHead : Term → Prop
  | uconst (i : native_Nat) (T : Term) : UHead (Term.UConst i T)
  | app {g : Term} (x : Term) : UHead g → UHead (Term.Apply g x)

omit [LogosFacts] in
theorem toSmt_apply_uhead {f : Term} (h : UHead f) (y : Term) :
    __eo_to_smt (Term.Apply f y) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y) := by
  rcases h with _ | ⟨_, h⟩
  · rfl
  rcases h with _ | ⟨_, h⟩
  · rfl
  rcases h with _ | ⟨_, h⟩
  · rfl
  rcases h with _ | ⟨_, h⟩
  · rfl
  rename_i g _
  cases g <;> rfl

omit [LogosFacts] in
theorem toSmt_foldl_uhead : ∀ (xs : List Term) {f : Term}, UHead f →
    __eo_to_smt (xs.foldl Term.Apply f) = (xs.map __eo_to_smt).foldl SmtTerm.Apply (__eo_to_smt f)
  | [], _, _ => rfl
  | x :: xs, f, hf => by
    simp only [List.foldl, List.map]
    rw [toSmt_foldl_uhead xs (UHead.app x hf), toSmt_apply_uhead hf]

omit [LogosFacts] in
theorem toSmt_apply_uf (f : String) (T : TypeNode) (cs : Array Node) (h : 1 ≤ cs.size) :
    (Node.app (.node .APPLY_UF (.var f T)) cs).toSmt =
      (cs.toList.map Node.toSmt).foldl SmtTerm.Apply (Node.var f T).toSmt := by
  have h1 : decide (1 ≤ cs.size) = true := by simpa using h
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp only [Op.eoShape, nodeEoShape, AppShape.toEo, Arity.accepts, List.length_map, Array.length_toList,
    h1, ↓reduceIte]
  rw [show (Node.var f T).toEo = Term.UConst (constId f) T.toEo by rw [Node.toEo],
    toSmt_foldl_uhead _ (UHead.uconst _ _), List.map_map]
  rfl

omit [LogosFacts] in
theorem eval_apply_of {g x : SmtTerm} (M : SmtModel)
    (hg : (∃ s T, g = SmtTerm.UConst s T) ∨ ∃ a b, g = SmtTerm.Apply a b) :
    __smtx_model_eval M (SmtTerm.Apply g x) =
      __smtx_model_eval_apply M (__smtx_model_eval M g) (__smtx_model_eval M x) := by
  rcases hg with ⟨s, T, rfl⟩ | ⟨a, b, rfl⟩ <;> rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
/-- **An application of a function value has its value.** -/
theorem apply_sound {M : Model} {f a g : MVal} (h : M.apply f a = some g) :
    __smtx_model_eval_apply (toSmtModel M) (toVal f) (toVal a) = toVal g := by
  unfold Model.apply at h
  split at h
  · rename_i fid dom rng
    split at h
    · rename_i t ht
      split at h
      · rename_i hty
        simp only [Bool.and_eq_true, beq_iff_eq] at hty
        obtain ⟨rfl, rfl⟩ := hty
        have e1 : __smtx_model_eval_apply (toSmtModel M) (toVal (.fn fid t.dom t.rng)) (toVal a) =
            native_eval_fun_apply (toSmtModel M) ((fid : ℝ) + 1) t.dom t.rng (toVal a) := by
          cases a <;> rfl
        have hne : ((fid : ℝ) + 1) ≠ native_default_fun_id := by
          simp only [native_default_fun_id]; positivity
        have hex : ∃ k : ℕ, ((fid : ℝ) + 1) = (k : ℝ) + 1 := ⟨fid, rfl⟩
        have hc : ∀ p : (∃ k : ℕ, ((fid : ℝ) + 1) = (k : ℝ) + 1), Classical.choose p = fid := by
          intro hex
          have := Classical.choose_spec hex
          have h2 : ((Classical.choose hex : ℕ) : ℝ) = fid := by linarith
          exact_mod_cast h2
        have hp : (fun p : MVal × MVal => decide (toVal p.1 = toVal a)) = (fun p => p.1 == a) := by
          funext p
          by_cases e : p.1 = a
          · simp [e]
          · have : toVal p.1 ≠ toVal a := fun h => e (toVal_inj h)
            simp [e, this]
        rw [e1]
        simp only [native_eval_fun_apply, model_fun_lookup, toSmtModel, tableFun]
        simp only [hne, hex, ↓reduceIte, ↓reduceDIte, hc, ht, and_self, hp]
        cases hf : t.entries.find? (·.1 == a) with
        | none => simp only [hf] at h ⊢; cases h; rfl
        | some p => rcases p with ⟨_, w⟩; simp only [hf] at h ⊢; cases h; rfl
      · cases h
    · cases h
  · cases h

omit [LogosFacts] in
theorem applyAll_sound {M : Model} : ∀ (vs : List MVal) (ts : List SmtTerm) (h : SmtTerm) (f r : MVal),
    List.Forall₂ (fun t v => __smtx_model_eval (toSmtModel M) t = toVal v) ts vs →
    ((∃ s T, h = SmtTerm.UConst s T) ∨ ∃ a b, h = SmtTerm.Apply a b) →
    __smtx_model_eval (toSmtModel M) h = toVal f → M.applyAll f vs = some r → __smtx_model_eval (toSmtModel M) (ts.foldl SmtTerm.Apply h) = toVal r
  | [], [], h, f, r, .nil, _, hh, ha => by
    simp only [Model.applyAll, Option.some.injEq] at ha; subst ha; exact hh
  | v :: vs, t :: ts, h, f, r, .cons ht hr, hs, hh, ha => by
    simp only [Model.applyAll] at ha
    split at ha
    · rename_i g hg
      simp only [List.foldl]
      refine applyAll_sound vs ts _ g r hr (Or.inr ⟨_, _, rfl⟩) ?_ ha
      show __smtx_model_eval _ _ = _
      rw [eval_apply_of _ hs, hh, ht]
      exact apply_sound hg
    · cases ha

/-! ### The evaluation -/

/-- The evaluation at fuel `n` is sound. -/
def EvOk (M : Model) (n : Nat) : Prop :=
  ∀ t S, MemoOk M S → MemoOk M (M.ev n t S).2 ∧ ∀ v, (M.ev n t S).1 = some v → __smtx_model_eval (toSmtModel M) t.toSmt = toVal v

omit [LogosFacts] in
theorem evList_sound (M : Model) (n : Nat) (IH : EvOk M n) : ∀ (l : List Node) (S : Model.Memo),
    MemoOk M S → MemoOk M (M.evList n l S).2 ∧ ∀ vs, (M.evList n l S).1 = some vs → Vals M l vs
  | [], S, hS => by
    rw [Model.evList]
    exact ⟨hS, fun vs h => by cases h; exact .nil⟩
  | c :: cs, S, hS => by
    rw [Model.evList]
    obtain ⟨hS1, hv1⟩ := IH c S hS
    rcases e1 : M.ev n c S with ⟨r1, S1⟩
    rw [e1] at hS1 hv1
    try dsimp only
    cases r1 with
    | none => exact ⟨hS1, fun vs h => by cases h⟩
    | some v =>
      dsimp only
      obtain ⟨hS2, hv2⟩ := evList_sound M n IH cs S1 hS1
      rcases e2 : M.evList n cs S1 with ⟨r2, S2⟩
      rw [e2] at hS2 hv2
      try dsimp only
      cases r2 with
      | none => exact ⟨hS2, fun vs h => by cases h⟩
      | some vs => exact ⟨hS2, fun vs' h => by cases h; exact .cons (hv1 v rfl) (hv2 vs rfl)⟩

omit [LogosFacts] in
theorem evNode_sound (M : Model) (n : Nat) (IH : EvOk M n) (t : Node) (S : Model.Memo) (hS : MemoOk M S) :
    MemoOk M (M.evNode n t S).2 ∧ ∀ v, (M.evNode n t S).1 = some v → __smtx_model_eval (toSmtModel M) t.toSmt = toVal v := by
  unfold Model.evNode
  split
  · rename_i b
    exact ⟨hS, fun v h => by cases h; exact evalsTo_const _ b⟩
  · exact ⟨hS, fun v h => eval_var h⟩
  · rename_i cs
    split
    · rename_i hty
      obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
      rcases e1 : M.evList n cs.toList S with ⟨r1, S1⟩
      rw [e1] at hS1 hv1
      try dsimp only
      cases r1 with
      | none => exact ⟨hS1, fun v h => by cases h⟩
      | some vs =>
        refine ⟨hS1, fun v h => ?_⟩
        dsimp only at h
        split at h
        · rename_i h2
          cases h
          exact distinct_sound M (hv1 vs rfl) hty h2
        · cases h
    · exact ⟨hS, fun v h => by cases h⟩
  · rename_i k cs _
    obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
    rcases e1 : M.evList n cs.toList S with ⟨r1, S1⟩
    rw [e1] at hS1 hv1
    try dsimp only
    cases r1 with
    | none => exact ⟨hS1, fun v h => by cases h⟩
    | some vs => exact ⟨hS1, fun v h => combine_sound M (hv1 vs rfl) h⟩
  · rename_i f T cs
    cases hf : M.const f T with
    | none => exact ⟨hS, fun v h => by cases h⟩
    | some fv =>
      dsimp only
      obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
      rcases e1 : M.evList n cs.toList S with ⟨r1, S1⟩
      rw [e1] at hS1 hv1
      try dsimp only
      cases r1 with
      | none => exact ⟨hS1, fun v h => by cases h⟩
      | some vs =>
        refine ⟨hS1, fun v h => ?_⟩
        dsimp only at h
        split at h
        · cases h
        · rename_i hne
          have hvs := hv1 vs rfl
          have hlen : 1 ≤ cs.size := by
            have := hvs.length_eq
            cases vs with
            | nil => simp at hne
            | cons => simp at this; omega
          rw [toSmt_apply_uf f T cs hlen]
          refine applyAll_sound vs _ _ fv v ?_ (Or.inl ⟨_, _, toSmt_var f T⟩) (eval_var hf) h
          exact (List.forall₂_map_left_iff).2 hvs
  · exact ⟨hS, fun v h => by cases h⟩

omit [LogosFacts] in
/-- **The evaluation is sound**, at every fuel. -/
theorem ev_sound (M : Model) : ∀ n, EvOk M n
  | 0 => fun t S hS => by
    rw [Model.ev]
    exact ⟨hS, fun v h => by cases h⟩
  | n + 1 => fun t S hS => by
    rw [Model.ev]
    split
    · rename_i w hw
      exact ⟨hS, fun v h => hS t v (by dsimp only at h; rw [hw, h])⟩
    · obtain ⟨hS1, hv1⟩ := evNode_sound M n (ev_sound M n) t S hS
      rcases e1 : M.evNode n t S with ⟨r, S1⟩
      rw [e1] at hS1 hv1
      exact ⟨memoOk_insert hS1 hv1, hv1⟩

omit [LogosFacts] in
theorem eval_andChain_true (M : Model) : ∀ (xs : List Term),
    (∀ x ∈ xs, __smtx_model_eval (toSmtModel M) (__eo_to_smt x) = SmtValue.Boolean true) →
    __smtx_model_eval (toSmtModel M) (__eo_to_smt (andChain xs)) = SmtValue.Boolean true
  | [], _ => eval_true _
  | x :: xs, h => by
    rw [toSmt_andChain_cons, eval_and, h x (by simp), eval_andChain_true M xs (fun y hy => h y (by simp [hy]))]
    rfl

omit [LogosFacts] in
theorem vals_true {M : Model} : ∀ {l : List Node} {vs : List MVal}, Vals M l vs →
    (∀ v ∈ vs, v = .bool true) → ∀ a ∈ l, __smtx_model_eval (toSmtModel M) a.toSmt = SmtValue.Boolean true
  | _, _, .nil, _ => by simp
  | _, _, .cons h hr, hv => by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := hv _ (List.mem_cons.2 (Or.inl rfl))
      rw [h, hb]; rfl
    · exact vals_true hr (fun v hv' => hv v (by simp [hv'])) a ha

/-- **A model that satisfies the assertions shows that they are
satisfiable**: its Logos model is well formed, and their conjunction is true
in it. -/
theorem satisfies_sound {M : Model} {as : List Node} (h : M.satisfies as = true) :
    model_wf (toSmtModel M) ∧ TrueIn (toSmtModel M) (Preprocess.inputNode as).toEo := by
  unfold Model.satisfies at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨ht, hc⟩, he⟩ := h
  refine ⟨toSmtModel_wf hc ht, ?_⟩
  obtain ⟨-, hv⟩ := evList_sound M Model.fuel (ev_sound M _) as {} (memoOk_empty M)
  rcases e : M.evList Model.fuel as {} with ⟨r, S⟩
  rw [e] at he hv
  cases r with
  | none => simp at he
  | some vs =>
    simp only [List.all_eq_true, beq_iff_eq] at he
    have htrue := vals_true (hv vs rfl) he
    unfold TrueIn Preprocess.inputNode Node.mkNode
    rw [toEo_and _ (by simp)]
    apply eval_andChain_true
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rcases (by simpa using ha : a ∈ as ∨ a = Node.mkTrue) with ha | rfl
    · exact htrue a ha
    · exact evalsTo_const _ true

end Telos.Solver

namespace Telos.Frontend

open Preprocess

variable [LogosFacts]

/-- **`solveScript`'s `sat` answers are correct**: the assertions are
satisfiable, in the Logos model of the model found. -/
theorem solveScript_sat (sc : Script) (u : UserOptions) (ee pp wp co : Bool)
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co = .ok (out, r))
    (hs : r.answer = .sat) {opts : PPOptions} {as : List Node}
    (hin : ppInput sc u = .ok (opts, as)) :
    ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
  simp only [solveScript, hin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      generalize Solver.run _ _ = r0 at hs
      split at hs
      · rename_i hne
        simp [hs] at hne
      · split at hs
        · rename_i hsat
          exact ⟨_, Solver.satisfies_sound hsat⟩
        · simp at hs

end Telos.Frontend
