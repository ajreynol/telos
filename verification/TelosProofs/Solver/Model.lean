import TelosProofs.Solver.Solve
import Telos.Solver.Model
import TelosProofs.Solver.Regex

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

/-- A canonical map updated at `i` to `e` (`__smtx_map_update_aux` with the
map's default). -/
noncomputable abbrev upd (m : SmtMap) (i e : SmtValue) : SmtMap :=
  __smtx_map_update_aux (__smtx_map_get_default m) m i e

/-- The Logos value of a value. A set is the empty map updated to `true` at
each of its elements, in order; an ill-typed one is `NotValue`. -/
noncomputable def toVal : MVal → SmtValue
  | .bool b => .Boolean b
  | .uval s i => .UValue s (i : ℝ)
  | .fn fid d r => .Fun ((fid : ℝ) + 1) d r
  | .dtc s dd i => .DtCons s dd i
  | .app f a => .Apply (toVal f) (toVal a)
  | .int i => .Numeral i
  | .rat q => .Real (q : ℝ)
  | .sempty T => .Set (SmtMap.default T (.Boolean false))
  | .sins e s =>
    if s.isSet then
      match s.ty with
      | .Set T =>
        if e.ty = T then
          match toVal s with
          | .Set m => .Set (upd m (toVal e) (.Boolean true))
          | _ => .NotValue
        else .NotValue
      | _ => .NotValue
    else .NotValue
  | .str w => .Seq (native_pack_string (w.map MVal.clampChar))
  | .re r => .RegLan r.toS

/-! ### Strings -/

omit [LogosFacts] in
theorem clampChar_valid (c : Nat) : native_char_valid (MVal.clampChar c) = true := by
  unfold MVal.clampChar native_char_valid
  split <;> simp_all

omit [LogosFacts] in
theorem clamp_all (w : List Nat) : ∀ c ∈ w.map MVal.clampChar, native_char_valid c = true := by
  intro c hc
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
  exact clampChar_valid d

omit [LogosFacts] in
theorem pack_chars_typeof : ∀ (w : List Nat), (∀ c ∈ w, native_char_valid c = true) →
    __smtx_typeof_seq_value (native_pack_seq SmtType.Char (w.map SmtValue.Char)) = .Seq .Char
  | [], _ => rfl
  | c :: w, h => by
    have ih := pack_chars_typeof w (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hc := h c (List.mem_cons_self ..)
    simp only [List.map_cons, native_pack_seq, __smtx_typeof_seq_value, ih, __smtx_typeof_value, hc,
      native_ite, native_Teq, ↓reduceIte]
    rfl

omit [LogosFacts] in
theorem pack_chars_canonical (uc : SmtUSortDom) : ∀ (w : List Nat), (∀ c ∈ w, native_char_valid c = true) →
    __smtx_seq_canonical uc (native_pack_seq SmtType.Char (w.map SmtValue.Char)) = true
  | [], _ => rfl
  | c :: w, h => by
    have ih := pack_chars_canonical uc w (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hc := h c (List.mem_cons_self ..)
    simp only [List.map_cons, native_pack_seq, __smtx_seq_canonical, __smtx_value_canonical, hc, ih, native_and,
      Bool.and_self]

omit [LogosFacts] in
theorem unpack_pack (T : SmtType) : ∀ l, native_unpack_seq (native_pack_seq T l) = l
  | [] => rfl
  | v :: l => by simp only [native_pack_seq, native_unpack_seq, unpack_pack T l]

omit [LogosFacts] in
theorem elem_pack (T : SmtType) : ∀ l, __smtx_elem_typeof_seq_value (native_pack_seq T l) = T
  | [] => rfl
  | v :: l => by simp only [native_pack_seq, __smtx_elem_typeof_seq_value, elem_pack T l]

omit [LogosFacts] in
theorem pack_inj (T : SmtType) (l1 l2 : List SmtValue) : native_pack_seq T l1 = native_pack_seq T l2 ↔ l1 = l2 := by
  constructor
  · intro h
    have := congrArg native_unpack_seq h
    simpa only [unpack_pack] using this

  · rintro rfl; rfl

omit [LogosFacts] in
theorem concatV_sound {a b r : MVal} (h : Model.concatV a b = some r) :
    __smtx_model_eval_str_concat (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.concatV, reduceCtorEq, Option.some.injEq] at h
  subst h
  simp only [toVal, __smtx_model_eval_str_concat, native_pack_string, unpack_pack, elem_pack, native_seq_concat,
    List.map_append]

omit [LogosFacts] in
theorem unpack_pack_string (l : List Nat) : native_unpack_string (native_pack_string l) = l := by
  simp only [native_unpack_string, native_pack_string, unpack_pack, List.map_map]
  induction l with
  | nil => rfl
  | cons c l ih => simp_all [impl_native_ssm_char_of_value]

omit [LogosFacts] in
theorem clampChar_lt (c : Nat) : MVal.clampChar c < 196608 := by
  unfold MVal.clampChar; split <;> omega

omit [LogosFacts] in
theorem clampChar_of_lt {c : Nat} (h : c < 196608) : MVal.clampChar c = c := by
  unfold MVal.clampChar; simp [h]

omit [LogosFacts] in
theorem strCode_eq (w : List Nat) :
    native_str_to_code (w.map MVal.clampChar) = Model.strCode w := by
  match w with
  | [] => rfl
  | [c] => simp [native_str_to_code, Model.strCode, clampChar_valid]
  | _ :: _ :: _ => rfl

omit [LogosFacts] in
theorem strCode_sound (w : List Nat) :
    __smtx_model_eval_str_to_code (toVal (.str w)) = .Numeral (Model.strCode w) := by
  simp only [toVal, __smtx_model_eval_str_to_code, unpack_pack_string, strCode_eq]

omit [LogosFacts] in
theorem lower_sound (w : List Nat) :
    __smtx_model_eval_str_to_lower (toVal (.str w)) =
      toVal (.str ((w.map MVal.clampChar).map Model.charToLower)) := by
  simp only [toVal, __smtx_model_eval_str_to_lower, unpack_pack_string, native_str_to_lower, List.map_map]
  congr 2
  apply List.map_congr_left
  intro c _
  have hl : Model.charToLower (MVal.clampChar c) < 196608 := by
    have := clampChar_lt c
    unfold Model.charToLower
    split <;> (simp_all; try omega)
  simp only [Function.comp, clampChar_of_lt hl]
  simp [impl_native_char_to_lower, Model.charToLower]

omit [LogosFacts] in
theorem upper_sound (w : List Nat) :
    __smtx_model_eval_str_to_upper (toVal (.str w)) =
      toVal (.str ((w.map MVal.clampChar).map Model.charToUpper)) := by
  simp only [toVal, __smtx_model_eval_str_to_upper, unpack_pack_string, native_str_to_upper, List.map_map]
  congr 2
  apply List.map_congr_left
  intro c _
  have hl : Model.charToUpper (MVal.clampChar c) < 196608 := by
    have := clampChar_lt c
    unfold Model.charToUpper
    split <;> (simp_all; try omega)
  simp only [Function.comp, clampChar_of_lt hl]
  simp [impl_native_char_to_upper, Model.charToUpper]

omit [LogosFacts] in
theorem rev_sound (w : List Nat) :
    __smtx_model_eval_str_rev (toVal (.str w)) = toVal (.str w.reverse) := by
  simp only [toVal, __smtx_model_eval_str_rev, native_pack_string, unpack_pack, elem_pack, native_seq_rev,
    List.map_reverse]

omit [LogosFacts] in
theorem extract_sound (w : List Nat) (i n : Int) :
    __smtx_model_eval_str_substr (toVal (.str w)) (.Numeral i) (.Numeral n) =
      toVal (.str (Model.strExtract w i n)) := by
  simp only [toVal, __smtx_model_eval_str_substr, native_pack_string, unpack_pack, elem_pack,
    native_seq_extract, Model.strExtract, List.length_map]
  split <;> simp [List.map_take, List.map_drop]

/-- The universe of the sorts of `toSmtModel`. -/
abbrev univ : SmtUSortDom := fun _ => (Set.univ : Set ModelId)

/-- **The map of a well-typed set**: canonical, of `Bool` values on `T`, with
default `false`, whose lookup at `w` is whether `w` is (the Logos value of) one
of the set's elements. -/
structure SetMap (v : MVal) (T : SmtType) (m : SmtMap) : Prop where
  val : toVal v = .Set m
  canon : __smtx_map_canonical univ m = true
  typed : __smtx_typeof_map_value m = .Map T .Bool
  dflt : __smtx_map_get_default m = .Boolean false
  leaf : mapLeaf m = .default T (.Boolean false)
  lookup : ∀ w, __smtx_map_lookup m w = .Boolean (decide (∃ e ∈ v.elems, toVal e = w))

theorem set_canonical_of {m : SmtMap} (hc : __smtx_map_canonical univ m = true)
    (hd : __smtx_map_get_default m = .Boolean false) :
    __smtx_value_canonical univ (.Set m) = true := by
  simp [__smtx_value_canonical, hc, hd, native_and, native_veq]

/-- **The values' types and canonicity, and the maps of sets.** -/
theorem toVal_props : ∀ v : MVal,
    __smtx_typeof_value (toVal v) = v.ty ∧ __smtx_value_canonical univ (toVal v) = true ∧
      (∀ T, v.isSet = true → v.ty = .Set T → ∃ m, SetMap v T m)
  | .bool _ | .int _ | .rat _ | .dtc .. => by
    refine ⟨?_, ?_, fun _ h => by simp [MVal.isSet] at h⟩ <;> simp [toVal, MVal.ty, __smtx_typeof_value, __smtx_value_canonical] <;> rfl
  | .str w => by
    refine ⟨?_, ?_, fun _ h => by simp [MVal.isSet] at h⟩
    · simp only [toVal, MVal.ty, __smtx_typeof_value, native_pack_string]
      exact pack_chars_typeof _ (clamp_all w)
    · simp only [toVal, __smtx_value_canonical, native_pack_string]
      exact pack_chars_canonical _ _ (clamp_all w)
  | .uval .. | .fn .. => by
    refine ⟨?_, ?_, fun _ h => by simp [MVal.isSet] at h⟩ <;>
      simp [toVal, MVal.ty, __smtx_typeof_value, __smtx_value_canonical, native_usort_mem]
  | .re r => by
    refine ⟨?_, ?_, fun _ h => by simp [MVal.isSet] at h⟩
    · rfl
    · simp only [toVal, __smtx_value_canonical]; exact TRe.toS_canonical r
  | .app f a => by
    obtain ⟨hf1, hf2, -⟩ := toVal_props f
    obtain ⟨ha1, ha2, -⟩ := toVal_props a
    refine ⟨?_, ?_, fun _ h => by simp [MVal.isSet] at h⟩
    · simp only [toVal, MVal.ty, __smtx_typeof_value, hf1, ha1]
    · simp only [toVal, __smtx_value_canonical, hf2, ha2, native_and, Bool.and_self]
  | .sempty T => by
    have hm : SetMap (.sempty T) T (SmtMap.default T (.Boolean false)) :=
      ⟨rfl, by simp [__smtx_map_canonical, __smtx_map_default_canonical, __smtx_value_canonical,
          __smtx_typeof_value, __smtx_type_default, native_ite, native_veq, native_and],
        rfl, rfl, rfl, fun w => by simp [__smtx_map_lookup, MVal.elems]⟩
    refine ⟨?_, set_canonical_of hm.canon hm.dflt, fun U _ hU => ?_⟩
    · simp [toVal, MVal.ty, __smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type]
    · simp only [MVal.ty, SmtType.Set.injEq] at hU; subst hU; exact ⟨_, hm⟩
  | .sins e s => by
    obtain ⟨he1, he2, -⟩ := toVal_props e
    obtain ⟨-, -, hs3⟩ := toVal_props s
    -- the well-typed case
    have key : ∀ T, s.isSet = true → s.ty = .Set T → e.ty = T → ∃ m, SetMap (.sins e s) T m := by
      intro T hsSet hsT heT
      obtain ⟨m, hm⟩ := hs3 T hsSet hsT
      refine ⟨upd m (toVal e) (.Boolean true), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [toVal, hsSet, hsT, heT, ite_true, hm.val]
      · exact LogosFacts.map_update_canonical univ m _ _ hm.canon he2 (by simp [__smtx_value_canonical])
      · exact LogosFacts.map_update_typed m T .Bool _ _ hm.typed (he1.trans heT) rfl
      · rw [LogosFacts.map_update_default, hm.dflt]
      · rw [LogosFacts.map_update_leaf, hm.leaf]
      · intro w
        by_cases hw : toVal e = w
        · subst hw
          rw [LogosFacts.map_lookup_update_same univ m _ _ hm.canon]
          simp [MVal.elems]
        · rw [LogosFacts.map_lookup_update_other univ m _ _ _ hm.canon (by simp [native_veq, hw]), hm.lookup w]
          simp [MVal.elems, hw]
    -- the type of `sins e s`, and its value when it is not a set
    by_cases hw : ∃ T, s.isSet = true ∧ s.ty = .Set T ∧ e.ty = T
    · obtain ⟨T, hsSet, hsT, heT⟩ := hw
      obtain ⟨m, hm⟩ := key T hsSet hsT heT
      have hty : (MVal.sins e s).ty = .Set T := by simp [MVal.ty, hsSet, hsT, heT]
      refine ⟨?_, ?_, fun U _ hU => ?_⟩
      · rw [hm.val, hty]; simp [__smtx_typeof_value, hm.typed, __smtx_map_to_set_type]
      · rw [hm.val]; exact set_canonical_of hm.canon hm.dflt
      · rw [hty] at hU; simp only [SmtType.Set.injEq] at hU; subst hU; exact ⟨m, hm⟩
    · have hnv : toVal (.sins e s) = .NotValue := by
        simp only [toVal]
        split
        · rename_i hsSet
          split
          · rename_i T hsT
            split
            · rename_i heT; exact absurd ⟨T, hsSet, hsT, heT⟩ hw
            · rfl
          · rfl
        · rfl
      have hty : (MVal.sins e s).ty = .None := by
        simp only [MVal.ty]
        split
        · rename_i hsSet
          split
          · rename_i T hsT
            split
            · rename_i heT; exact absurd ⟨T, hsSet, hsT, by simpa using heT⟩ hw
            · rfl
          · rfl
        · rfl
      refine ⟨?_, ?_, fun U _ hU => by rw [hty] at hU; cases hU⟩
      · rw [hnv, hty]; rfl
      · rw [hnv]; rfl
termination_by v => sizeOf v

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
    match M.lookup k.name k.ty with
    | some v => toVal v
    | none => __smtx_type_default k.ty
  nativeFuns := tableFun M
  usortDom := fun _ => Set.univ

/-- `toSmtModel`, with the values of the bound variables of `env` pushed
(`native_model_push`, `toSmtModelE_push`). -/
noncomputable def toSmtModelE (M : Model) (env : Model.Env) : SmtModel where
  values k :=
    if k.isVar then
      match env.lookup k.name k.ty with
      | some v => toVal v
      | none => __smtx_type_default k.ty
    else
    match M.lookup k.name k.ty with
    | some v => toVal v
    | none => __smtx_type_default k.ty
  nativeFuns := tableFun M
  usortDom := fun _ => Set.univ

omit [LogosFacts] in
theorem toSmtModelE_nil (M : Model) : toSmtModelE M [] = toSmtModel M := by
  simp only [toSmtModelE, toSmtModel, Model.Env.lookup]

omit [LogosFacts] in
/-- Pushing a value on the model of `env` gives that of the longer `env`. -/
theorem toSmtModelE_push (M : Model) (env : Model.Env) (s : native_String) (T : SmtType) (v : MVal) :
    native_model_push (toSmtModelE M env) s T (toVal v) = toSmtModelE M ((s, T, v) :: env) := by
  simp only [native_model_push, toSmtModelE]
  congr 1
  funext k
  rcases k with ⟨isVar, name, ty⟩
  cases isVar with
  | false => simp
  | true =>
    by_cases h : name = s ∧ ty = T
    · obtain ⟨rfl, rfl⟩ := h
      simp [Model.Env.lookup]
    · have h1 : ¬ ({ isVar := true, name := name, ty := ty } : SmtModelKey) = { isVar := true, name := s, ty := T } := by
        intro e; cases e; exact h ⟨rfl, rfl⟩
      have h2 : (s == name && T == ty) = false := by
        rw [Bool.eq_false_iff]; intro e
        simp only [Bool.and_eq_true, beq_iff_eq] at e
        exact h ⟨e.1.symm, e.2.symm⟩
      simp only [h1, ↓reduceIte, Model.Env.lookup, h2, Bool.false_eq_true]

omit [LogosFacts] in
theorem usort_dom_wf_univ : usort_dom_wf (fun _ => (Set.univ : Set ModelId)) := by
  intro i
  refine ⟨Set.mem_univ _, fun _ n => ⟨(n : ℝ), Set.mem_univ _, ?_⟩⟩
  simp

theorem typeof_toVal (v : MVal) : __smtx_typeof_value (toVal v) = v.ty := (toVal_props v).1

theorem canonical_toVal (v : MVal) :
    __smtx_value_canonical (fun _ => (Set.univ : Set ModelId)) (toVal v) = true := (toVal_props v).2.1

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
  simp only [Bool.and_eq_true] at h
  have h := h.1
  rw [List.all_eq_true] at h
  have hm : (k, (T, v)) ∈ M.consts.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.2 (by simpa using hk)
  simpa using h _ hm

omit [LogosFacts] in
/-- A symbol looked up has a value of its type. -/
theorem lookup_ty {M : Model} (h : M.constsOk = true) {x : native_String} {T : SmtType} {v : MVal}
    (hk : M.lookup x T = some v) : v.ty = T := by
  unfold Model.constsOk at h
  simp only [Bool.and_eq_true] at h
  unfold Model.lookup at hk
  split at hk
  · rename_i y U w hf
    cases hk
    have hm := Array.mem_of_find?_eq_some hf
    have hp := Array.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [Array.all_eq_true_iff_forall_mem] at h
    have := h.2 _ hm
    simp only [beq_iff_eq] at this
    rw [this, hp.2]
  · split at hk
    · rename_i T' w hc
      split at hk
      · rename_i hT
        cases hk
        rw [← beq_iff_eq.1 hT]
        exact constsOk_get (by unfold Model.constsOk; simp only [Bool.and_eq_true]; exact h) hc
      · cases hk
    · cases hk

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
      · rename_i v hk
        rw [typeof_toVal]; exact lookup_ty hc hk
      · exact (default_ok hT).1
  · intro isVar s T hT
    simp only [toSmtModel]
    split
    · exact (default_ok hT).2
    · split
      · exact canonical_toVal _
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

variable {env : Model.Env}

/-- The memo has the values of its nodes in the model. -/
def MemoOk (M : Model) (env : Model.Env) (S : Model.Memo) : Prop :=
  ∀ t v, S.get? ⟨t⟩ = some (some v) → __smtx_model_eval (toSmtModelE M env) t.toSmt = toVal v

omit [LogosFacts] in
theorem memoOk_empty (M : Model) (env : Model.Env) : MemoOk M env {} := by
  intro t v h; simp at h

omit [LogosFacts] in
theorem memoOk_insert {M : Model} {S : Model.Memo} (hS : MemoOk M env S) {t : Node} {r : Option MVal}
    (ht : ∀ v, r = some v → __smtx_model_eval (toSmtModelE M env) t.toSmt = toVal v) : MemoOk M env (S.insert ⟨t⟩ r) := by
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
    __smtx_model_eval (toSmtModelE M env) (Node.var x T).toSmt = toVal v := by
  unfold Model.const at h
  rw [toSmt_var, __smtx_model_eval.eq_def]
  simp only [native_model_lookup, model_key, toSmtModelE, Bool.false_eq_true, ↓reduceIte, h]

omit [LogosFacts] in
theorem toSmt_boundVar (x : String) (T : TypeNode) :
    (Node.boundVar x T).toSmt = SmtTerm.Var (native_string_lit x) (tyS T) := by
  unfold Node.toSmt; rw [Node.toEo]; rfl

omit [LogosFacts] in
theorem eval_boundVar {M : Model} {x : String} {T : TypeNode} {v : MVal}
    (h : env.lookup (native_string_lit x) (tyS T) = some v) :
    __smtx_model_eval (toSmtModelE M env) (Node.boundVar x T).toSmt = toVal v := by
  rw [toSmt_boundVar, __smtx_model_eval.eq_def]
  simp only [native_model_var_lookup, toSmtModelE, ↓reduceIte, h]

/-! ### Connectives -/

omit [LogosFacts] in
theorem eval_eq' (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) = __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

/-! ### Equality of values -/

/-- The Logos value of a set is a set's, or `NotValue`; of anything else,
neither. -/
theorem toVal_set_shape (v : MVal) (h : v.isSet = true) :
    (∃ m, toVal v = .Set m) ∨ toVal v = .NotValue := by
  cases v <;> simp [MVal.isSet] at h
  · exact .inl ⟨_, rfl⟩
  · rename_i e s
    simp only [toVal]
    split
    · split
      · split
        · split
          · exact .inl ⟨_, rfl⟩
          · exact .inr rfl
        · exact .inr rfl
      · exact .inr rfl
    · exact .inr rfl

theorem toVal_nonset_shape (v : MVal) (h : v.isSet = false) :
    (∀ m, toVal v ≠ .Set m) ∧ toVal v ≠ .NotValue := by
  cases v <;> simp_all [MVal.isSet, toVal]

theorem toVal_not_reglan (v : MVal) (hv : v.isRe = false) (r : SmtRegLan) : toVal v ≠ .RegLan r := by
  by_cases h : v.isSet = true
  · rcases toVal_set_shape v h with ⟨m, hm⟩ | hm <;> rw [hm] <;> simp
  · cases v <;> simp_all [MVal.isSet, MVal.isRe, toVal]

/-- A set's type is a set type, or none. -/
theorem set_ty_shape (v : MVal) (h : v.isSet = true) : (∃ T, v.ty = .Set T) ∨ v.ty = .None := by
  cases v <;> simp [MVal.isSet] at h
  · exact .inl ⟨_, rfl⟩
  · simp only [MVal.ty]
    split
    · split
      · split
        · exact .inl ⟨_, rfl⟩
        · exact .inr rfl
      · exact .inr rfl
    · exact .inr rfl

/-- A set translates to a Logos set exactly when it is well typed. -/
theorem toVal_set_none (v : MVal) (hT : v.ty = .None) : toVal v = .NotValue ∨ v.isSet = false := by
  cases v with
  | sempty T => simp [MVal.ty] at hT
  | sins e s =>
    left
    simp only [MVal.ty] at hT
    simp only [toVal]
    split
    · rename_i hsSet
      simp only [hsSet, ↓reduceIte] at hT
      split
      · rename_i T hsT
        rw [hsT] at hT
        split
        · rename_i heT; simp [heT] at hT
        · rfl
      · rfl
    · rfl
  | _ => right; rfl

/-- Two sets' maps have the same lookups exactly when the sets have the same
elements (as Logos values). -/
theorem lookups_iff {a b : MVal} {T U : SmtType} {ma mb : SmtMap} (ha : SetMap a T ma) (hb : SetMap b U mb) :
    (∀ w, __smtx_map_lookup ma w = __smtx_map_lookup mb w) ↔
      (∀ e ∈ a.elems, ∃ f ∈ b.elems, toVal e = toVal f) ∧ (∀ f ∈ b.elems, ∃ e ∈ a.elems, toVal f = toVal e) := by
  simp only [ha.lookup, hb.lookup, SmtValue.Boolean.injEq, decide_eq_decide]
  constructor
  · intro h
    refine ⟨fun e he => ?_, fun f hf => ?_⟩
    · obtain ⟨f, hf, hfe⟩ := (h (toVal e)).1 ⟨e, he, rfl⟩
      exact ⟨f, hf, hfe.symm⟩
    · obtain ⟨e, he, hef⟩ := (h (toVal f)).2 ⟨f, hf, rfl⟩
      exact ⟨e, he, hef.symm⟩
  · intro ⟨h1, h2⟩ w
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨f, hf, hef⟩ := h1 e he
      exact ⟨f, hf, hef.symm⟩
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨e, he, hfe⟩ := h2 f hf
      exact ⟨e, he, hfe.symm⟩

/-- **`veq` is Logos's equality of values.** -/
theorem veq_iff (a b : MVal) : MVal.veq a b = true ↔ toVal a = toVal b := by
  by_cases hab : (a.isSet || b.isSet) = true
  · rw [MVal.veq.eq_def]
    simp only [hab, ↓reduceIte]
    by_cases hboth : (a.isSet && b.isSet) = true
    · simp only [hboth, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have ha : a.isSet = true := by simp_all
      have hb : b.isSet = true := by simp_all
      by_cases hwa : a.ty = .None <;> by_cases hwb : b.ty = .None
      · -- both ill typed: both `NotValue`
        have h1 := (toVal_set_none a hwa).resolve_right (by simp [ha])
        have h2 := (toVal_set_none b hwb).resolve_right (by simp [hb])
        simp [hwa, hwb, h1, h2]
      · rcases set_ty_shape b hb with ⟨U, hU⟩ | hU
        · obtain ⟨mb, hmb⟩ := (toVal_props b).2.2 U hb hU
          have h1 := (toVal_set_none a hwa).resolve_right (by simp [ha])
          simp [hwa, hwb, h1, hmb.val]
        · exact absurd hU hwb
      · rcases set_ty_shape a ha with ⟨T, hT⟩ | hT
        · obtain ⟨ma, hma⟩ := (toVal_props a).2.2 T ha hT
          have h2 := (toVal_set_none b hwb).resolve_right (by simp [hb])
          simp [hwa, hwb, h2, hma.val]
        · exact absurd hT hwa
      · rcases set_ty_shape a ha with ⟨T, hT⟩ | hT
        · rcases set_ty_shape b hb with ⟨U, hU⟩ | hU
          · obtain ⟨ma, hma⟩ := (toVal_props a).2.2 T ha hT
            obtain ⟨mb, hmb⟩ := (toVal_props b).2.2 U hb hU
            simp only [hT, hU, hma.val, hmb.val]
            simp only [show (T.Set != SmtType.None) = true from rfl, show (U.Set != SmtType.None) = true from rfl,
              Bool.and_self, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, SmtType.Set.injEq, List.all_eq_true,
              List.any_eq_true, List.mem_attach, true_and, Subtype.forall, Subtype.exists, SmtValue.Set.injEq,
              forall_const]
            -- the elements, by `veq_iff` on them
            have IH1 : ∀ e ∈ a.elems, ∀ f ∈ b.elems, MVal.veq e f = true ↔ toVal e = toVal f :=
              fun e _ f _ => veq_iff e f
            have IH2 : ∀ f ∈ b.elems, ∀ e ∈ a.elems, MVal.veq f e = true ↔ toVal f = toVal e :=
              fun f _ e _ => veq_iff f e
            constructor
            · rintro ⟨⟨rfl, h1⟩, h2⟩
              apply LogosFacts.map_ext univ ma mb hma.canon hmb.canon (by rw [hma.leaf, hmb.leaf])
              refine (lookups_iff hma hmb).2 ⟨fun e he => ?_, fun f hf => ?_⟩
              · obtain ⟨f, hf, hv⟩ := h1 e he
                exact ⟨f, hf, (IH1 e he f hf).1 hv⟩
              · obtain ⟨e, he, hv⟩ := h2 f hf
                exact ⟨e, he, (IH2 f hf e he).1 hv⟩
            · intro hm
              subst hm
              have hTU : T = U := by
                have := hma.typed.symm.trans hmb.typed
                simpa using this
              subst hTU
              obtain ⟨h1, h2⟩ := (lookups_iff hma hmb).1 (fun _ => rfl)
              refine ⟨⟨rfl, fun e he => ?_⟩, fun f hf => ?_⟩
              · obtain ⟨f, hf, hv⟩ := h1 e he
                exact ⟨f, hf, (IH1 e he f hf).2 hv⟩
              · obtain ⟨e, he, hv⟩ := h2 f hf
                exact ⟨e, he, (IH2 f hf e he).2 hv⟩
          · exact absurd hU hwb
        · exact absurd hT hwa
    · -- one set, one not
      simp only [hboth, Bool.not_false, ↓reduceIte, Bool.false_eq_true, false_iff]
      intro he
      by_cases ha : a.isSet = true
      · have hb : b.isSet = false := by simp_all
        obtain ⟨h1, h2⟩ := toVal_nonset_shape b hb
        rcases toVal_set_shape a ha with ⟨m, hm⟩ | hm
        · exact h1 m (he.symm.trans hm)
        · exact h2 (he.symm.trans hm)
      · have ha' : a.isSet = false := by simpa using ha
        have hb : b.isSet = true := by simp_all
        obtain ⟨h1, h2⟩ := toVal_nonset_shape a ha'
        rcases toVal_set_shape b hb with ⟨m, hm⟩ | hm
        · exact h1 m (he.trans hm)
        · exact h2 (he.trans hm)
  · have ha : a.isSet = false := by simp_all
    have hb : b.isSet = false := by simp_all
    cases a <;> cases b <;> simp [MVal.isSet] at ha hb
    case app.app f x g y =>
      rw [MVal.veq.eq_def]
      simp only [MVal.isSet, Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
      rw [veq_iff f g, veq_iff x y]
      simp [toVal]
    case str.str x y =>
      rw [MVal.veq.eq_def]
      simp only [MVal.isSet, Bool.or_self, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, toVal,
        native_pack_string, SmtValue.Seq.injEq, pack_inj]
      constructor
      · intro h; rw [h]
      · intro h; exact List.map_injective_iff.2 (fun a b e => by cases e; rfl) h
    case re.re x y =>
      rw [MVal.veq.eq_def]
      simp only [MVal.isSet, Bool.or_self, Bool.false_eq_true, ↓reduceIte, toVal, SmtValue.RegLan.injEq]
      exact TRe.ceq_iff x y
    all_goals (rw [MVal.veq.eq_def]; simp [MVal.isSet, toVal])
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := MVal.sizeOf_lt_of_mem_elems ‹_ ∈ a.elems›; have := MVal.sizeOf_lt_of_mem_elems ‹_ ∈ b.elems›; omega)
    | omega

/-! ### Sets -/

theorem sins_ty {e s : MVal} {T : SmtType} (h : (MVal.sins e s).ty = .Set T) :
    s.isSet = true ∧ s.ty = .Set T ∧ e.ty = T := by
  simp only [MVal.ty] at h
  split at h
  · rename_i hs
    split at h
    · rename_i U hU
      split at h
      · rename_i he; simp only [SmtType.Set.injEq] at h; subst h; exact ⟨hs, hU, by simpa using he⟩
      · cases h
    · cases h
  · cases h

/-- The elements of a well-typed set have its element type. -/
theorem elems_ty : ∀ {v : MVal} {T : SmtType}, v.isSet = true → v.ty = .Set T → ∀ e ∈ v.elems, e.ty = T
  | .sempty _, _, _, _, e, he => by simp [MVal.elems] at he
  | .sins a s, T, _, h, e, he => by
    obtain ⟨hs, hsT, haT⟩ := sins_ty h
    simp only [MVal.elems, List.mem_cons] at he
    rcases he with rfl | he
    · exact haT
    · exact elems_ty hs hsT e he

theorem insAll_props {s : MVal} {T : SmtType} (hs : s.isSet = true) (hT : s.ty = .Set T) :
    ∀ (es : List MVal), (∀ e ∈ es, e.ty = T) →
      (s.insAll es).isSet = true ∧ (s.insAll es).ty = .Set T ∧ (s.insAll es).elems = es ++ s.elems
  | [], _ => by simpa [MVal.insAll] using ⟨hs, hT⟩
  | e :: es, h => by
    obtain ⟨h1, h2, h3⟩ := insAll_props hs hT es (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have he := h e (List.mem_cons_self ..)
    refine ⟨rfl, ?_, ?_⟩
    · show (MVal.sins e (s.insAll es)).ty = _
      simp [MVal.ty, h1, h2, he]
    · show (MVal.sins e (s.insAll es)).elems = _
      simp [MVal.elems, h3]

/-- `__smtx_set_op_rec` keeps the default leaf of its accumulator. -/
theorem set_op_rec_leaf (b : native_Bool) : ∀ (m1 m2 acc : SmtMap),
    mapLeaf (__smtx_set_op_rec b m1 m2 acc) = mapLeaf acc
  | SmtMap.default _ _, _, _ => by simp [__smtx_set_op_rec]
  | SmtMap.cons e _ m1, m2, acc => by
    simp only [__smtx_set_op_rec]
    rw [set_op_rec_leaf b m1 m2]
    unfold native_ite
    split <;> simp [LogosFacts.map_update_leaf]

/-- The map of a canonical set value. -/
theorem canon_of_value {m : SmtMap} (h : __smtx_value_canonical univ (.Set m) = true) :
    __smtx_map_canonical univ m = true := by
  simp [__smtx_value_canonical, native_and] at h; exact h.1

/-- **A Logos set operation, on maps of sets, has the map of a set** with the
expected lookups. -/
theorem set_result {r : MVal} {T : SmtType} {m : SmtMap} (hr : SetMap r T m) {m' : SmtMap}
    (hc : __smtx_map_canonical univ m' = true) (hl : mapLeaf m' = .default T (.Boolean false))
    (hk : ∀ v, __smtx_map_lookup m' v = __smtx_map_lookup m v) : SmtValue.Set m' = toVal r := by
  rw [hr.val, LogosFacts.map_ext univ m' m hc hr.canon (by rw [hl, hr.leaf]) hk]

theorem singleton_sound {x r : MVal} (h : some (MVal.sins x (.sempty x.ty)) = some r) :
    __smtx_model_eval_set_singleton (toVal x) = toVal r := by
  cases h
  simp only [toVal, MVal.isSet, MVal.ty, ite_true]
  simp [__smtx_model_eval_set_singleton, upd, __smtx_map_update_aux, __smtx_map_update_aux_no_default,
    __smtx_map_get_default, native_ite, native_veq, typeof_toVal]

theorem setOp_sound {a b r : MVal} {f : SmtType → Option MVal} (h : Model.combine.setOp a b f = some r)
    {op : SmtValue → SmtValue → SmtValue}
    (hop : ∀ T ma mb, a.isSet = true → b.isSet = true → a.ty = .Set T → b.ty = .Set T →
      SetMap a T ma → SetMap b T mb → ∀ r', f T = some r' → op (.Set ma) (.Set mb) = toVal r') :
    op (toVal a) (toVal b) = toVal r := by
  unfold Model.combine.setOp at h
  split at h
  · rename_i T U hT hU
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨ha, hb⟩, rfl⟩ := hc
      obtain ⟨ma, hma⟩ := (toVal_props a).2.2 T ha hT
      obtain ⟨mb, hmb⟩ := (toVal_props b).2.2 T hb hU
      rw [hma.val, hmb.val]
      exact hop T ma mb ha hb hT hU hma hmb r h
    · cases h
  · cases h

theorem union_sound {a b r : MVal} (h : Model.combine.setOp a b (fun _ => some (b.insAll a.elems)) = some r) :
    __smtx_model_eval_set_union (toVal a) (toVal b) = toVal r := by
  refine setOp_sound h (fun T ma mb ha hb hT hU hma hmb r' hr' => ?_)
  cases hr'
  obtain ⟨hi, hty, hel⟩ := insAll_props hb hU a.elems (elems_ty ha hT)
  obtain ⟨mr, hmr⟩ := (toVal_props _).2.2 T hi hty
  have hcan := LogosFacts.set_union_canonical univ _ _ (set_canonical_of hma.canon hma.dflt)
    (set_canonical_of hmb.canon hmb.dflt)
  simp only [__smtx_model_eval_set_union, __smtx_set_union] at hcan ⊢
  refine set_result hmr (canon_of_value hcan) (by rw [set_op_rec_leaf, hmb.leaf]) (fun v => ?_)
  rw [LogosFacts.set_union_lookup univ ma mb T v hma.typed hmb.typed hma.canon hmb.canon hma.dflt,
    hma.lookup, hmb.lookup, hmr.lookup, hel]
  by_cases h1 : ∃ e ∈ a.elems, toVal e = v <;> simp [native_ite, native_veq, h1, List.mem_append, or_and_right,
    exists_or]

theorem any_veq_iff (e : MVal) (l : List MVal) :
    l.any (e.veq ·) = true ↔ ∃ f ∈ l, toVal f = toVal e := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨f, hf, hv⟩; exact ⟨f, hf, ((veq_iff e f).1 hv).symm⟩
  · rintro ⟨f, hf, hfe⟩; exact ⟨f, hf, (veq_iff e f).2 hfe.symm⟩

/-- An intersection or a difference: the elements of `a` kept by `keep`
(whether they are in `b`), into the empty set. -/
theorem filter_sound {a b r : MVal} {T : SmtType} (keep : Bool → Bool)
    (ha : a.isSet = true) (hT : a.ty = .Set T)
    (hr : (MVal.sempty T).insAll (a.elems.filter fun e => keep (b.elems.any (e.veq ·))) = r)
    {m' : SmtMap} (hc : __smtx_map_canonical univ m' = true) (hl : mapLeaf m' = .default T (.Boolean false))
    (hk : ∀ v, __smtx_map_lookup m' v =
      .Boolean (decide ((∃ e ∈ a.elems, toVal e = v) ∧ keep (decide (∃ f ∈ b.elems, toVal f = v)) = true))) :
    SmtValue.Set m' = toVal r := by
  subst hr
  have hes : ∀ e ∈ a.elems.filter (fun e => keep (b.elems.any (e.veq ·))), e.ty = T :=
    fun e he => elems_ty ha hT e (List.mem_of_mem_filter he)
  obtain ⟨hi, hty, hel⟩ := insAll_props (s := .sempty T) rfl rfl _ hes
  obtain ⟨mr, hmr⟩ := (toVal_props _).2.2 T hi hty
  refine set_result hmr hc hl (fun v => ?_)
  rw [hk, hmr.lookup, hel]
  congr 1
  rw [decide_eq_decide]
  simp only [MVal.elems, List.append_nil, List.mem_filter]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hkp⟩
    refine ⟨e, ⟨he, ?_⟩, rfl⟩
    have : b.elems.any (e.veq ·) = decide (∃ f ∈ b.elems, toVal f = toVal e) := by
      rw [Bool.eq_iff_iff, any_veq_iff, decide_eq_true_eq]
    rw [this]; exact hkp
  · rintro ⟨e, ⟨he, hkp⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, ?_⟩
    have : b.elems.any (e.veq ·) = decide (∃ f ∈ b.elems, toVal f = toVal e) := by
      rw [Bool.eq_iff_iff, any_veq_iff, decide_eq_true_eq]
    rw [← this]; exact hkp

theorem inter_sound {a b r : MVal}
    (h : Model.combine.setOp a b
      (fun T => some ((MVal.sempty T).insAll (a.elems.filter fun e => b.elems.any (e.veq ·)))) = some r) :
    __smtx_model_eval_set_inter (toVal a) (toVal b) = toVal r := by
  refine setOp_sound h (fun T ma mb ha _ hT _ hma hmb r' hr' => ?_)
  have hcan := LogosFacts.set_inter_canonical univ _ _ (set_canonical_of hma.canon hma.dflt)
    (set_canonical_of hmb.canon hmb.dflt)
  simp only [__smtx_model_eval_set_inter, __smtx_set_inter] at hcan ⊢
  refine filter_sound id ha hT (Option.some.inj hr') (canon_of_value hcan)
    (by rw [set_op_rec_leaf, hma.typed]; rfl) (fun v => ?_)
  rw [LogosFacts.set_inter_lookup univ ma mb T v hma.typed hmb.typed hma.canon hma.dflt, hma.lookup, hmb.lookup]
  by_cases h1 : ∃ e ∈ a.elems, toVal e = v <;> by_cases h2 : ∃ f ∈ b.elems, toVal f = v <;>
    simp [native_ite, native_veq, native_and, h1, h2]

theorem minus_sound {a b r : MVal}
    (h : Model.combine.setOp a b
      (fun T => some ((MVal.sempty T).insAll (a.elems.filter fun e => !b.elems.any (e.veq ·)))) = some r) :
    __smtx_model_eval_set_minus (toVal a) (toVal b) = toVal r := by
  refine setOp_sound h (fun T ma mb ha _ hT _ hma hmb r' hr' => ?_)
  have hcan := LogosFacts.set_minus_canonical univ _ _ (set_canonical_of hma.canon hma.dflt)
    (set_canonical_of hmb.canon hmb.dflt)
  simp only [__smtx_model_eval_set_minus, __smtx_set_minus] at hcan ⊢
  refine filter_sound (! ·) ha hT (Option.some.inj hr') (canon_of_value hcan)
    (by rw [set_op_rec_leaf, hma.typed]; rfl) (fun v => ?_)
  rw [LogosFacts.set_minus_lookup univ ma mb T v hma.typed hmb.typed hma.canon hma.dflt, hma.lookup, hmb.lookup]
  by_cases h1 : ∃ e ∈ a.elems, toVal e = v <;> by_cases h2 : ∃ f ∈ b.elems, toVal f = v <;>
    simp [native_ite, native_veq, native_and, native_not, h1, h2]

theorem member_sound {x s r : MVal}
    (h : (match s.ty with
      | .Set _ => if s.isSet then some (MVal.bool (s.elems.any (x.veq ·))) else none
      | _ => none) = some r) :
    __smtx_model_eval_set_member (toVal x) (toVal s) = toVal r := by
  split at h
  · rename_i T hT
    split at h
    · rename_i hs
      cases h
      obtain ⟨m, hm⟩ := (toVal_props s).2.2 T hs hT
      simp only [__smtx_model_eval_set_member, __smtx_map_select, hm.val, hm.lookup, toVal]
      congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_eq, any_veq_iff]
    · cases h
  · cases h

/-- Only an ill-typed set is `NotValue`. -/
theorem toVal_ne_notValue (v : MVal) (h : v.notValue = false) : toVal v ≠ .NotValue := by
  by_cases hs : v.isSet = true
  · have hT : v.ty ≠ .None := by simpa [MVal.notValue, hs] using h
    rcases set_ty_shape v hs with ⟨T, hT'⟩ | hT'
    · obtain ⟨m, hm⟩ := (toVal_props v).2.2 T hs hT'
      rw [hm.val]; simp
    · exact absurd hT' hT
  · exact (toVal_nonset_shape v (by simpa using hs)).2

theorem eval_eq_of_not_reglan (v w : SmtValue) (h : ∀ r, v ≠ .RegLan r) :
    __smtx_model_eval_eq v w = SmtValue.Boolean (native_veq v w) := by
  cases v <;> simp_all [__smtx_model_eval_eq]

theorem eval_eq_toVal (a b : MVal) (ha : a.isRe = false) :
    __smtx_model_eval_eq (toVal a) (toVal b) = SmtValue.Boolean (a.veq b) := by
  rw [eval_eq_of_not_reglan _ _ (toVal_not_reglan a ha)]
  congr 1
  by_cases h : a.veq b = true
  · simp [native_veq, (veq_iff a b).1 h, h]
  · have : toVal a ≠ toVal b := fun e => h ((veq_iff a b).2 e)
    simp [native_veq, this, h]

/-- Each node has the value of its value in the model. -/
abbrev ValsIn (N : SmtModel) (l : List Node) (vs : List MVal) : Prop :=
  List.Forall₂ (fun c v => __smtx_model_eval N c.toSmt = toVal v) l vs

abbrev Vals (M : Model) (env : Model.Env) (l : List Node) (vs : List MVal) : Prop := ValsIn (toSmtModelE M env) l vs

omit [LogosFacts] in
theorem vals_map {N : SmtModel} : ∀ {l : List Node} {vs : List MVal}, ValsIn N l vs →
    List.Forall₂ (fun x v => __smtx_model_eval N (__eo_to_smt x) = toVal v) (l.map Node.toEo) vs
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h (vals_map hr)

omit [LogosFacts] in
theorem eval_andChain_vals (N : SmtModel) : ∀ (xs : List Term) (vs : List MVal) (bs : List Bool),
    List.Forall₂ (fun x v => __smtx_model_eval N (__eo_to_smt x) = toVal v) xs vs →
    Model.bools vs = some bs →
    __smtx_model_eval N (__eo_to_smt (andChain xs)) = SmtValue.Boolean (bs.all id)
  | [], [], bs, .nil, h => by
    simp only [Model.bools, Option.some.injEq] at h; subst h
    exact eval_true _
  | x :: xs, v :: vs, bs, .cons hx hr, h => by
    cases v with
    | bool b =>
      simp only [Model.bools] at h
      obtain ⟨bs', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [toSmt_andChain_cons, eval_and, hx, eval_andChain_vals N xs vs bs' hr hb']
      simp [toVal, __smtx_model_eval_and, native_and]
    | _ => simp [Model.bools] at h

omit [LogosFacts] in
theorem eval_orChain_vals (N : SmtModel) : ∀ (xs : List Term) (vs : List MVal) (bs : List Bool),
    List.Forall₂ (fun x v => __smtx_model_eval N (__eo_to_smt x) = toVal v) xs vs →
    Model.bools vs = some bs →
    __smtx_model_eval N (__eo_to_smt (orChain xs)) = SmtValue.Boolean (bs.any id)
  | [], [], bs, .nil, h => by
    simp only [Model.bools, Option.some.injEq] at h; subst h
    exact eval_false _
  | x :: xs, v :: vs, bs, .cons hx hr, h => by
    cases v with
    | bool b =>
      simp only [Model.bools] at h
      obtain ⟨bs', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [toSmt_orChain_cons, eval_or, hx, eval_orChain_vals N xs vs bs' hr hb']
      simp [toVal, __smtx_model_eval_or, native_or]
    | _ => simp [Model.bools] at h

/-! ### Arithmetic -/

omit [LogosFacts] in
theorem plusV_sound {a b r : MVal} (h : Model.plusV a b = some r) :
    __smtx_model_eval_plus (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.plusV, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [toVal, __smtx_model_eval_plus, native_zplus, native_rplus]

omit [LogosFacts] in
theorem multV_sound {a b r : MVal} (h : Model.multV a b = some r) :
    __smtx_model_eval_mult (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.multV, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [toVal, __smtx_model_eval_mult, native_zmult, native_rmult]

omit [LogosFacts] in
theorem subV_sound {a b r : MVal} (h : Model.subV a b = some r) :
    __smtx_model_eval__ (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.subV, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [toVal, __smtx_model_eval__, native_zplus, native_zneg, native_rplus, native_rneg]

omit [LogosFacts] in
theorem divV_sound (N : SmtModel) {a b r : MVal} (h : Model.divV a b = some r) :
    (__smtx_model_eval_ite
      (__smtx_model_eval_eq (__smtx_to_real_coerce (toVal b)) (SmtValue.Real (native_mk_real 0 1)))
      (__smtx_model_eval_apply N (native_model_lookup N native_qdiv_by_zero_id
        (SmtType.FunType SmtType.Real SmtType.Real)) (__smtx_to_real_coerce (toVal a)))
      (__smtx_model_eval_qdiv_total (__smtx_to_real_coerce (toVal a)) (__smtx_to_real_coerce (toVal b)))) =
    toVal r := by
  cases a <;> cases b <;> simp only [Model.divV, reduceCtorEq] at h
  rename_i qa qb
  split at h
  · cases h
  · rename_i hb
    simp only [Option.some.injEq] at h
    subst h
    have hb' : (qb : ℝ) ≠ 0 := by exact_mod_cast (by simpa using hb)
    simp [toVal, __smtx_to_real_coerce, __smtx_model_eval_eq, native_veq, native_mk_real, hb',
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total, native_rdiv_total]

omit [LogosFacts] in
theorem negV_sound {a r : MVal} (h : Model.negV a = some r) :
    __smtx_model_eval_uneg (toVal a) = toVal r := by
  cases a <;> simp only [Model.negV, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [toVal, __smtx_model_eval_uneg, native_zneg, native_rneg]

omit [LogosFacts] in
theorem ltV_sound {a b r : MVal} (h : Model.ltV a b = some r) :
    __smtx_model_eval_lt (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.ltV, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [toVal, __smtx_model_eval_lt, native_zlt, native_rlt]

omit [LogosFacts] in
theorem leqV_sound {a b r : MVal} (h : Model.leqV a b = some r) :
    __smtx_model_eval_leq (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.leqV, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [toVal, __smtx_model_eval_leq, native_zleq, native_rleq]

omit [LogosFacts] in
/-- A right-associated chain of `op` evaluates as `chainV` computes it. -/
theorem eval_opChain (N : SmtModel) (op : UserOp) (f : MVal → MVal → Option MVal)
    (sm : SmtTerm → SmtTerm → SmtTerm) (fe : SmtValue → SmtValue → SmtValue)
    (htr : ∀ x y, __eo_to_smt (eoApp2 op x y) = sm (__eo_to_smt x) (__eo_to_smt y))
    (hev : ∀ x y, __smtx_model_eval N (sm x y) = fe (__smtx_model_eval N x) (__smtx_model_eval N y))
    (hf : ∀ a b r, f a b = some r → fe (toVal a) (toVal b) = toVal r)
    (nil : Term) (nv : MVal) (hnil : __smtx_model_eval N (__eo_to_smt nil) = toVal nv) :
    ∀ (xs : List Term) (vs : List MVal) (r : MVal),
    List.Forall₂ (fun x v => __smtx_model_eval N (__eo_to_smt x) = toVal v) xs vs →
    Model.chainV f nv vs = some r →
    __smtx_model_eval N (__eo_to_smt (eoRightAssocNil op nil xs)) = toVal r
  | [], [], r, .nil, h => by
    simp only [Model.chainV, Option.some.injEq] at h; subst h; exact hnil
  | x :: xs, v :: vs, r, .cons hx hr, h => by
    simp only [Model.chainV, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hr'⟩ := h
    rw [eoRightAssocNil, htr, hev, hx, eval_opChain N op f sm fe htr hev hf nil nv hnil xs vs w hr hw]
    exact hf v w r hr'

omit [LogosFacts] in
theorem toEo_typedChain {k : Kind} {op : UserOp} (hk : k.eoShape = .rightAssocNil op .typed)
    (cs : Array Node) (h : 2 ≤ cs.size) :
    (Node.app (.kind k) cs).toEo = eoRightAssocNil op (typedNil op cs[0].toEo) (cs.toList.map Node.toEo) := by
  rw [Node.toEo_app]
  have hhead : (cs.toList.map Node.toEo).headD Term.Stuck = cs[0].toEo := by
    rcases cs with ⟨l⟩
    cases l with
    | nil => simp at h
    | cons a l => rfl
  simp only [Op.eoShape, hk, AppShape.toEo, List.length_map, Array.length_toList, h, ↓reduceIte, Nil.eval, hhead]

omit [LogosFacts] in
theorem eval_numeral_term (N : SmtModel) (i : Int) :
    __smtx_model_eval N (__eo_to_smt (Term.Numeral i)) = SmtValue.Numeral i := by
  rw [show __eo_to_smt (Term.Numeral i) = SmtTerm.Numeral i from rfl, __smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem eval_rational_term (N : SmtModel) (q : Rat) :
    __smtx_model_eval N (__eo_to_smt (Term.Rational q)) = SmtValue.Real (native_rat_to_real q) := by
  rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q from rfl, __smtx_model_eval.eq_def]

omit [LogosFacts] in
/-- The typed nil of a chain evaluates to `chainNil`'s value. -/
theorem eval_typedNil (N : SmtModel) (k : Kind) (op : UserOp) (x : Node) (nv : MVal)
    (hop : (k = .ADD ∧ op = UserOp.plus) ∨ (k = .MULT ∧ op = UserOp.mult))
    (h : Model.chainNil k x.smtTypeF = some nv) :
    __smtx_model_eval N (__eo_to_smt (typedNil op x.toEo)) = toVal nv := by
  rw [Node.smtTypeF_eq] at h
  change Model.chainNil k (__smtx_typeof x.toSmt) = some nv at h
  unfold typedNil
  have hx : __eo_to_smt x.toEo = x.toSmt := rfl
  rw [hx]
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · revert h
    cases __smtx_typeof x.toSmt <;> simp only [Model.chainNil, reduceCtorEq, false_implies, Option.some.injEq] <;>
      intro h <;> subst h <;>
      simp [typedNilOfType, eval_numeral_term, eval_rational_term, toVal, native_rat_to_real, native_mk_rational]

omit [LogosFacts] in
/-- The nil of a chain of `str.++` evaluates to the empty string. -/
theorem eval_typedNil_concat (N : SmtModel) (x : Node) (nv : MVal)
    (h : Model.chainNil .STRING_CONCAT x.smtTypeF = some nv) :
    __smtx_model_eval N (__eo_to_smt (typedNil UserOp.str_concat x.toEo)) = toVal nv := by
  rw [Node.smtTypeF_eq] at h
  change Model.chainNil .STRING_CONCAT (__smtx_typeof x.toSmt) = some nv at h
  unfold typedNil
  have hx : __eo_to_smt x.toEo = x.toSmt := rfl
  rw [hx]
  revert h
  cases __smtx_typeof x.toSmt <;> simp only [Model.chainNil, reduceCtorEq, false_implies]
  rename_i E
  cases E <;> simp only [reduceCtorEq, false_implies, Option.some.injEq]
  intro h
  subst h
  simp only [typedNilOfType]
  rw [show __eo_to_smt (Term.String []) = SmtTerm.String [] from rfl, __smtx_model_eval.eq_def]
  rfl

omit [LogosFacts] in
theorem toSmt_bin {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 2))
    {cs : Array Node} (h : cs.size = 2) :
    (Node.app (.kind k) cs).toSmt = __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) cs[0].toEo) cs[1].toEo) := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_two h]
  simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
theorem toSmt_un {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 1))
    {cs : Array Node} (h : cs.size = 1) :
    (Node.app (.kind k) cs).toSmt = __eo_to_smt (Term.Apply (Term.UOp op) cs[0].toEo) := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_one h]
  simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
theorem toSmt_tern {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 3))
    {cs : Array Node} (h : cs.size = 3) :
    (Node.app (.kind k) cs).toSmt =
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) cs[0].toEo) cs[1].toEo) cs[2].toEo) := by
  unfold Node.toSmt
  rw [Node.toEo_app, toList_three h]
  simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

/-! ### Regular expressions -/

omit [LogosFacts] in
theorem clampChar_eq : MVal.clampChar = reClamp := rfl

omit [LogosFacts] in
theorem unpack_str (w : List Nat) :
    native_unpack_seq (native_pack_string (w.map MVal.clampChar)) = (w.map reClamp).map SmtValue.Char := by
  simp only [native_pack_string, unpack_pack, clampChar_eq]

omit [LogosFacts] in
theorem reConcatV_sound {a b r : MVal} (h : Model.reConcatV a b = some r) :
    __smtx_model_eval_re_concat (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.reConcatV, reduceCtorEq, Option.some.injEq] at h
  subst h
  simp [toVal, __smtx_model_eval_re_concat, TRe.mkConcat_toS]

omit [LogosFacts] in
theorem reUnionV_sound {a b r : MVal} (h : Model.reUnionV a b = some r) :
    __smtx_model_eval_re_union (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.reUnionV, reduceCtorEq, Option.some.injEq] at h
  subst h
  simp [toVal, __smtx_model_eval_re_union, TRe.mkUnion_toS]

omit [LogosFacts] in
theorem reInterV_sound {a b r : MVal} (h : Model.reInterV a b = some r) :
    __smtx_model_eval_re_inter (toVal a) (toVal b) = toVal r := by
  cases a <;> cases b <;> simp only [Model.reInterV, reduceCtorEq, Option.some.injEq] at h
  subst h
  simp [toVal, __smtx_model_eval_re_inter, TRe.mkInter_toS]

omit [LogosFacts] in
theorem toEo_constChain {k : Kind} {op : UserOp} {nil : Term} (hk : k.eoShape = .rightAssocNil op (.const nil))
    (cs : Array Node) (h : 2 ≤ cs.size) :
    (Node.app (.kind k) cs).toEo = eoRightAssocNil op nil (cs.toList.map Node.toEo) := by
  rw [Node.toEo_app]
  simp only [Op.eoShape, hk, AppShape.toEo, List.length_map, Array.length_toList, h, ↓reduceIte, Nil.eval]

omit [LogosFacts] in
theorem toSmt_nul {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 0))
    {cs : Array Node} (h : cs.size = 0) :
    (Node.app (.kind k) cs).toSmt = __eo_to_smt (Term.UOp op) := by
  have : cs.toList = [] := by simpa using h
  unfold Node.toSmt
  rw [Node.toEo_app, this]
  simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
/-- **A regular expression operation has its value.** -/
theorem combineRe_sound_in (N : SmtModel) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : ValsIn N cs.toList vs) (h : Model.combineRe k vs = some r) :
    __smtx_model_eval N (Node.app (.kind k) cs).toSmt = toVal r := by
  have hlen : cs.size = vs.length := by simpa using hv.length_eq
  unfold Model.combineRe at h
  split at h
  · -- `re.++`
    split at h
    · have hs : 2 ≤ cs.size := by omega
      unfold Node.toSmt
      rw [toEo_constChain (op := UserOp.re_concat) rfl cs hs]
      exact eval_opChain N UserOp.re_concat Model.reConcatV SmtTerm.re_concat __smtx_model_eval_re_concat
        (fun _ _ => rfl) (fun _ _ => by rw [__smtx_model_eval.eq_def]) (fun _ _ _ => reConcatV_sound) _ _
        (by rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
              SmtTerm.str_to_re (SmtTerm.String []) from rfl, __smtx_model_eval.eq_def]
            simp only
            rw [__smtx_model_eval.eq_def]; rfl) _ _ _ (vals_map hv) h
    · cases h
  · -- `re.union`
    split at h
    · have hs : 2 ≤ cs.size := by omega
      unfold Node.toSmt
      rw [toEo_constChain (op := UserOp.re_union) rfl cs hs]
      exact eval_opChain N UserOp.re_union Model.reUnionV SmtTerm.re_union __smtx_model_eval_re_union
        (fun _ _ => rfl) (fun _ _ => by rw [__smtx_model_eval.eq_def]) (fun _ _ _ => reUnionV_sound) _ _
        (by rw [show __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none from rfl, __smtx_model_eval.eq_def]
            rfl) _ _ _ (vals_map hv) h
    · cases h
  · -- `re.inter`
    split at h
    · have hs : 2 ≤ cs.size := by omega
      unfold Node.toSmt
      rw [toEo_constChain (op := UserOp.re_inter) rfl cs hs]
      exact eval_opChain N UserOp.re_inter Model.reInterV SmtTerm.re_inter __smtx_model_eval_re_inter
        (fun _ _ => rfl) (fun _ _ => by rw [__smtx_model_eval.eq_def]) (fun _ _ _ => reInterV_sound) _ _
        (by rw [show __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all from rfl, __smtx_model_eval.eq_def]
            rfl) _ _ _ (vals_map hv) h
    · cases h
  all_goals first
    | (cases h; done)
    | skip
  -- the nullary operations
  all_goals first
    | (have hs : cs.size = 0 := by simpa using hlen
       cases h
       first
       | (rw [toSmt_nul (op := UserOp.re_none) rfl hs,
            show __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none from rfl, __smtx_model_eval.eq_def]; rfl)
       | (rw [toSmt_nul (op := UserOp.re_all) rfl hs,
            show __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all from rfl, __smtx_model_eval.eq_def]; rfl)
       | (rw [toSmt_nul (op := UserOp.re_allchar) rfl hs,
            show __eo_to_smt (Term.UOp UserOp.re_allchar) = SmtTerm.re_allchar from rfl, __smtx_model_eval.eq_def]; rfl))
    | skip
  -- the unary and binary operations
  all_goals first
    | (have hs : cs.size = 1 := by simpa using hlen
       rw [toList_one hs] at hv
       obtain ⟨h0, -⟩ := List.forall₂_cons.1 hv
       cases h
       first
       | (rw [toSmt_un (op := UserOp.str_to_re) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) x)
            = SmtTerm.str_to_re (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          simp only [toVal, __smtx_model_eval_str_to_re, unpack_str, TRe.ofList_toS])
       | (rw [toSmt_un (op := UserOp.re_mult) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) x)
            = SmtTerm.re_mult (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          simp only [toVal, __smtx_model_eval_re_mult, TRe.mkStar_toS])
       | (rw [toSmt_un (op := UserOp.re_plus) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) x)
            = SmtTerm.re_plus (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          simp only [toVal, __smtx_model_eval_re_plus, __smtx_model_eval_re_mult, __smtx_model_eval_re_concat,
            TRe.mkStar_toS, TRe.mkConcat_toS])
       | (rw [toSmt_un (op := UserOp.re_opt) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) x)
            = SmtTerm.re_opt (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          simp only [toVal, __smtx_model_eval_re_opt, __smtx_model_eval_re_union, TRe.mkUnion_toS]; rfl)
       | (rw [toSmt_un (op := UserOp.re_comp) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) x)
            = SmtTerm.re_comp (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          simp only [toVal, __smtx_model_eval_re_comp, TRe.mkComp_toS]))
    | (have hs : cs.size = 2 := by simpa using hlen
       rw [toList_two hs] at hv
       obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
       cases h
       first
       | (rw [toSmt_bin (op := UserOp.str_in_re) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y)
            = SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [toVal, __smtx_model_eval_str_in_re, unpack_str, TRe.inRe_toS])
       | (rw [toSmt_bin (op := UserOp.re_diff) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x) y)
            = SmtTerm.re_diff (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [toVal, __smtx_model_eval_re_diff, native_re_diff, TRe.mkInter_toS, TRe.mkComp_toS])
       | (rw [toSmt_bin (op := UserOp.re_range) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y)
            = SmtTerm.re_range (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [toVal, __smtx_model_eval_re_range, unpack_str, TRe.mkRange_toS]))

omit [LogosFacts] in
theorem exp_toS (r : TRe) : ∀ n, __smtx_re_exp_rec n (.RegLan r.toS) = .RegLan (r.exp n).toS
  | 0 => rfl
  | n + 1 => by
    simp only [__smtx_re_exp_rec, exp_toS r n, __smtx_model_eval_re_concat, TRe.exp, TRe.mkConcat_toS]

omit [LogosFacts] in
theorem loopRec_toS (lo : Int) (r : TRe) : ∀ n hi,
    __smtx_re_loop_rec n (.Numeral lo) (.Numeral hi) (.RegLan r.toS) = .RegLan (r.loopRec lo n hi).toS
  | 0, hi => by simp [__smtx_re_loop_rec, __smtx_model_eval_re_exp, exp_toS, TRe.loopRec, native_int_to_nat]
  | n + 1, hi => by
    simp only [__smtx_re_loop_rec, loopRec_toS lo r n, __smtx_model_eval_re_exp, exp_toS, native_zplus, native_zneg,
      __smtx_model_eval_re_union, TRe.loopRec, TRe.mkUnion_toS, native_int_to_nat]

omit [LogosFacts] in
/-- **An indexed operation has its value.** -/
theorem combineIdx_sound_in (N : SmtModel) {k : Kind} {is : Array Int} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : ValsIn N cs.toList vs) (h : Model.combineIdx k is.toList vs = some r) :
    __smtx_model_eval N (Node.app (.indexed k is) cs).toSmt = toVal r := by
  have hlen : cs.size = vs.length := by simpa using hv.length_eq
  unfold Model.combineIdx at h
  split at h
  · rename_i i rr his
    cases h
    have hs : cs.size = 1 := by simpa using hlen
    rw [toList_one hs] at hv
    obtain ⟨h0, -⟩ := List.forall₂_cons.1 hv
    unfold Node.toSmt
    rw [Node.toEo_app, toList_one hs]
    simp only [Op.eoShape, his, indexedEoShape, AppShape.toEo, Arity.accepts, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    simp only [show ((0 + 1 == 1) = true) from rfl, ↓reduceIte]
    rw [show ∀ x, __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp (Term.Numeral i)) x)
      = SmtTerm.re_exp (SmtTerm.Numeral i) (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
    simp only
    rw [← Node.toSmt, h0, __smtx_model_eval.eq_def]
    simp only [toVal, __smtx_model_eval_re_exp, exp_toS, native_int_to_nat]
  · rename_i i j rr his
    cases h
    have hs : cs.size = 1 := by simpa using hlen
    rw [toList_one hs] at hv
    obtain ⟨h0, -⟩ := List.forall₂_cons.1 hv
    unfold Node.toSmt
    rw [Node.toEo_app, toList_one hs]
    simp only [Op.eoShape, his, indexedEoShape, AppShape.toEo, Arity.accepts, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    simp only [show ((0 + 1 == 1) = true) from rfl, ↓reduceIte]
    rw [show ∀ x, __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral i) (Term.Numeral j)) x)
      = SmtTerm.re_loop (SmtTerm.Numeral i) (SmtTerm.Numeral j) (__eo_to_smt x) from fun _ => rfl,
      __smtx_model_eval.eq_def]
    simp only
    rw [← Node.toSmt, h0, __smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
    simp only [toVal, __smtx_model_eval_re_loop, __smtx_model_eval_gt, __smtx_model_eval_lt, native_zlt, TRe.loop,
      __smtx_model_eval_ite]
    by_cases hij : j < i
    · simp [hij, native_re_none, TRe.toS]
    · simp [hij, loopRec_toS, native_zplus, native_zneg, native_int_to_nat]
  · cases h

/-! ### The extended functions of strings -/

omit [LogosFacts] in
theorem strV (w : List Nat) : toVal (.str w) = .Seq (native_pack_seq .Char (TRe.chars w)) := by
  simp only [toVal, native_pack_string, TRe.chars, clampChar_eq]

omit [LogosFacts] in
theorem intV (i : Int) : toVal (.int i) = .Numeral i := rfl

omit [LogosFacts] in
theorem boolV (b : Bool) : toVal (.bool b) = .Boolean b := rfl

omit [LogosFacts] in
theorem reV (r : TRe) : toVal (.re r) = .RegLan r.toS := rfl

omit [LogosFacts] in
theorem validStr_sound {w : List Nat} {r : MVal} (h : Model.validStr w = some r) :
    toVal r = .Seq (native_pack_string w) := by
  unfold Model.validStr at h
  split at h
  · rename_i hw
    cases h
    simp only [toVal]
    congr 2
    rw [List.map_congr_left (g := id) (fun c hc => by
      simpa using clampChar_of_lt (by simpa using List.all_eq_true.1 hw c hc))]
    simp
  · cases h

/-- **An extended function of strings has its value.** -/
theorem combineStr_sound_in (N : SmtModel) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : ValsIn N cs.toList vs) (h : Model.combineStr k vs = some r) :
    __smtx_model_eval N (Node.app (.kind k) cs).toSmt = toVal r := by
  have hlen : cs.size = vs.length := by simpa using hv.length_eq
  unfold Model.combineStr at h
  split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals first
    | (have hs : cs.size = 2 := by simpa using hlen
       rw [toList_two hs] at hv
       obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
       obtain rfl := Option.some.inj h
       first
       | (rw [toSmt_bin (op := UserOp.str_at) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y)
            = SmtTerm.str_at (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          exact extract_sound _ _ 1)
       | (rw [toSmt_bin (op := UserOp.str_contains) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y)
            = SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [strV, __smtx_model_eval_str_contains, unpack_pack, native_seq_contains, native_seq_indexof, ← TRe.ofList_toS, TRe.indexOf_toS, boolV]; try rfl)
       | (rw [toSmt_bin (op := UserOp.str_prefixof) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y)
            = SmtTerm.str_prefixof (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [__smtx_model_eval_str_prefixof, show ∀ w : List Nat, __smtx_model_eval_str_len (toVal (.str w)) = .Numeral w.length from fun w => by
            simp [strV, __smtx_model_eval_str_len, native_seq_len, unpack_pack]]
          rw [extract_sound, eval_eq_toVal (.str _) (.str _) rfl]; try rfl)
       | (rw [toSmt_bin (op := UserOp.str_suffixof) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y)
            = SmtTerm.str_suffixof (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [__smtx_model_eval_str_suffixof, show ∀ w : List Nat, __smtx_model_eval_str_len (toVal (.str w)) = .Numeral w.length from fun w => by
            simp [strV, __smtx_model_eval_str_len, native_seq_len, unpack_pack], __smtx_model_eval__, native_zplus, native_zneg]
          rw [extract_sound, eval_eq_toVal (.str _) (.str _) rfl]; try rfl)
       | (rw [toSmt_bin (op := UserOp.str_lt) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x) y)
            = SmtTerm.str_lt (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [toVal, __smtx_model_eval_str_lt, unpack_pack_string, native_str_lt, Model.strLt])
       | (rw [toSmt_bin (op := UserOp.str_leq) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y)
            = SmtTerm.str_leq (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          simp only [__smtx_model_eval_str_leq]
          rw [eval_eq_toVal (.str _) (.str _) rfl]
          simp only [toVal, __smtx_model_eval_str_lt, unpack_pack_string, native_str_lt, Model.strLt, __smtx_model_eval_or, native_or]))
    | skip
  all_goals first
    | (have hs : cs.size = 3 := by simpa using hlen
       rw [toList_three hs] at hv
       obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h1, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h2, -⟩ := List.forall₂_cons.1 hv
       obtain rfl := Option.some.inj h
       first
       | (rw [toSmt_tern (op := UserOp.str_indexof) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
              = SmtTerm.str_indexof (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, intV, __smtx_model_eval_str_indexof, unpack_pack, native_seq_indexof, ← TRe.ofList_toS, TRe.indexOf_toS])
       | (rw [toSmt_tern (op := UserOp.str_indexof_re) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y) z)
              = SmtTerm.str_indexof_re (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, intV, reV, __smtx_model_eval_str_indexof_re, unpack_pack, TRe.indexOf_toS])
       | (rw [toSmt_tern (op := UserOp.str_replace) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y) z)
              = SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, __smtx_model_eval_str_replace, unpack_pack, elem_pack, native_seq_replace, ← TRe.ofList_toS, TRe.replace_toS])
       | (rw [toSmt_tern (op := UserOp.str_replace_re) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y) z)
              = SmtTerm.str_replace_re (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, reV, __smtx_model_eval_str_replace_re, unpack_pack, elem_pack, TRe.replace_toS])
       | (rw [toSmt_tern (op := UserOp.str_replace_all) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y) z)
              = SmtTerm.str_replace_all (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, __smtx_model_eval_str_replace_all, unpack_pack, elem_pack, native_seq_replace_all, ← TRe.ofList_toS, TRe.replaceAll_toS])
       | (rw [toSmt_tern (op := UserOp.str_replace_re_all) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y) z)
              = SmtTerm.str_replace_re_all (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, reV, __smtx_model_eval_str_replace_re_all, unpack_pack, elem_pack, TRe.replaceAll_toS])
       | (rw [toSmt_tern (op := UserOp.str_update) rfl hs, show ∀ x y z,
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
              = SmtTerm.str_update (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
          simp only [strV, intV, __smtx_model_eval_str_update, unpack_pack, elem_pack, native_seq_update, Model.strUpdate]
          congr 2
          simp only [TRe.chars, List.length_map]
          split <;> simp [List.map_take, List.map_drop]))
    | skip
  all_goals
    have hs : cs.size = 1 := by simpa using hlen
    rw [toList_one hs] at hv
    obtain ⟨h0, -⟩ := List.forall₂_cons.1 hv
  · rw [toSmt_un (op := UserOp.str_from_code) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) x)
            = SmtTerm.str_from_code (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, h0]
    rw [validStr_sound h]
    simp only [toVal, __smtx_model_eval_str_from_code, native_str_from_code]
    rfl
  · rw [toSmt_un (op := UserOp.str_to_int) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) x)
            = SmtTerm.str_to_int (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, h0]
    obtain rfl := Option.some.inj h
    simp only [toVal, __smtx_model_eval_str_to_int, unpack_pack_string]
    rfl
  · rw [toSmt_un (op := UserOp.str_from_int) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) x)
            = SmtTerm.str_from_int (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, h0]
    rw [validStr_sound h]
    simp only [toVal, __smtx_model_eval_str_from_int, native_str_from_int]
    rfl

/-- `divisible` on integers, as the evaluator has it. -/
theorem divisible_eval (k t : Int) :
    __smtx_model_eval_divisible (toVal (.int k)) (toVal (.int t)) = toVal (.bool (native_mod_total t k == 0)) := by
  simp only [toVal, __smtx_model_eval_divisible, __smtx_model_eval_mod_total, __smtx_model_eval_eq, native_veq]
  by_cases hz : native_mod_total t k = 0 <;> simp [hz]

/-- **A connective has its value.** -/
theorem combine_sound_in (N : SmtModel) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : ValsIn N cs.toList vs) (h : Model.combine k cs vs = some r) :
    __smtx_model_eval N (Node.app (.kind k) cs).toSmt = toVal r := by
  have hlen : cs.size = vs.length := by simpa using hv.length_eq
  unfold Model.combine at h
  split at h
  · exact combineRe_sound_in N hv h
  rename_i hnre
  split at h
  · exact combineStr_sound_in N hv h
  rename_i hnstr
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
      exact eval_andChain_vals N _ _ _ (vals_map hv) hbs
    · cases h
  · split at h
    · rename_i h2
      obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.1 h
      have hs : 2 ≤ cs.size := by omega
      unfold Node.toSmt
      rw [toEo_or cs hs]
      exact eval_orChain_vals N _ _ _ (vals_map hv) hbs
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
  · rename_i a b
    split at h
    · cases h
    rename_i hre
    cases h
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_eq hs, eval_eq', h0, h1, eval_eq_toVal a b (by simpa using hre)]
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
  · -- `+`
    split at h
    · rename_i h2
      obtain ⟨nv, hnv, hc⟩ := Option.bind_eq_some_iff.1 h
      have hs : 2 ≤ cs.size := by omega
      have h0 : (cs[0]?.getD default) = cs[0] := by simp [Array.getElem?_eq_getElem (by omega : 0 < cs.size)]
      rw [h0] at hnv
      unfold Node.toSmt
      rw [toEo_typedChain (op := UserOp.plus) rfl cs hs]
      exact eval_opChain N UserOp.plus Model.plusV SmtTerm.plus __smtx_model_eval_plus (fun _ _ => rfl)
        (fun _ _ => by rw [__smtx_model_eval.eq_def]) (fun _ _ _ => plusV_sound) _ nv
        (eval_typedNil N .ADD UserOp.plus cs[0] nv (.inl ⟨rfl, rfl⟩) hnv) _ _ _ (vals_map hv) hc
    · cases h
  · -- `*`
    split at h
    · rename_i h2
      obtain ⟨nv, hnv, hc⟩ := Option.bind_eq_some_iff.1 h
      have hs : 2 ≤ cs.size := by omega
      have h0 : (cs[0]?.getD default) = cs[0] := by simp [Array.getElem?_eq_getElem (by omega : 0 < cs.size)]
      rw [h0] at hnv
      unfold Node.toSmt
      rw [toEo_typedChain (op := UserOp.mult) rfl cs hs]
      exact eval_opChain N UserOp.mult Model.multV SmtTerm.mult __smtx_model_eval_mult (fun _ _ => rfl)
        (fun _ _ => by rw [__smtx_model_eval.eq_def]) (fun _ _ _ => multV_sound) _ nv
        (eval_typedNil N .MULT UserOp.mult cs[0] nv (.inr ⟨rfl, rfl⟩) hnv) _ _ _ (vals_map hv) hc
    · cases h
  · -- `str.++`
    split at h
    · rename_i h2
      obtain ⟨nv, hnv, hc⟩ := Option.bind_eq_some_iff.1 h
      have hs : 2 ≤ cs.size := by omega
      have h0 : (cs[0]?.getD default) = cs[0] := by simp [Array.getElem?_eq_getElem (by omega : 0 < cs.size)]
      rw [h0] at hnv
      unfold Node.toSmt
      rw [toEo_typedChain (op := UserOp.str_concat) rfl cs hs]
      exact eval_opChain N UserOp.str_concat Model.concatV SmtTerm.str_concat __smtx_model_eval_str_concat
        (fun _ _ => rfl) (fun _ _ => by rw [__smtx_model_eval.eq_def]) (fun _ _ _ => concatV_sound) _ nv
        (eval_typedNil_concat N cs[0] nv hnv) _ _ _ (vals_map hv) hc
    · cases h
  all_goals first
    | (cases h; done)
    | skip
  -- the binary and unary operations
  all_goals
    first
    | (have hs : cs.size = 2 := by simpa using hlen
       rw [toList_two hs] at hv
       obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
       first
       | (rw [toSmt_bin (op := UserOp.neg) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)
            = SmtTerm.neg (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact subV_sound h)
       | (rw [toSmt_bin (op := UserOp.qdiv) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)
            = SmtTerm.qdiv (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact divV_sound N h)
       | (rw [toSmt_bin (op := UserOp.lt) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y)
            = SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact ltV_sound h)
       | (rw [toSmt_bin (op := UserOp.leq) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y)
            = SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact leqV_sound h)
       | (rw [toSmt_bin (op := UserOp.gt) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y)
            = SmtTerm.gt (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact ltV_sound h)
       | (rw [toSmt_bin (op := UserOp.geq) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)
            = SmtTerm.geq (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact leqV_sound h)
       | (rw [toSmt_bin (op := UserOp.set_union) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y)
            = SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact union_sound h)
       | (rw [toSmt_bin (op := UserOp.set_inter) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y)
            = SmtTerm.set_inter (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact inter_sound h)
       | (rw [toSmt_bin (op := UserOp.set_minus) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y)
            = SmtTerm.set_minus (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact minus_sound h)
       | (rw [toSmt_bin (op := UserOp.set_member) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y)
            = SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact member_sound h)
       | (rw [toSmt_bin (op := UserOp.divisible) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y)
            = SmtTerm.divisible (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
          obtain rfl := Option.some.inj h
          exact divisible_eval _ _))
    | (have hs : cs.size = 1 := by simpa using hlen
       rw [toList_one hs] at hv
       obtain ⟨h0, -⟩ := List.forall₂_cons.1 hv
       first
       | (rw [toSmt_un (op := UserOp.__eoo_neg_2) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)
            = SmtTerm.uneg (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]; exact negV_sound h)
       | (rw [toSmt_un (op := UserOp.to_real) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x)
            = SmtTerm.to_real (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          try (obtain rfl := Option.some.inj h)
          simp [toVal, __smtx_model_eval_to_real, native_int_to_real, Rat.cast_intCast])
       | (rw [toSmt_un (op := UserOp.set_singleton) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) x)
            = SmtTerm.set_singleton (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]; exact singleton_sound h)
       | (rw [toSmt_un (op := UserOp.str_len) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) x)
            = SmtTerm.str_len (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          obtain rfl := Option.some.inj h
          simp [toVal, __smtx_model_eval_str_len, native_seq_len, native_pack_string, unpack_pack])
       | (rw [toSmt_un (op := UserOp.str_to_code) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) x)
            = SmtTerm.str_to_code (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          obtain rfl := Option.some.inj h
          exact strCode_sound _)
       | (rw [toSmt_un (op := UserOp.str_is_digit) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) x)
            = SmtTerm.str_is_digit (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          obtain rfl := Option.some.inj h
          simp only [__smtx_model_eval_str_is_digit, strCode_sound]
          simp [toVal, __smtx_model_eval_leq, __smtx_model_eval_and, native_and, native_zleq])
       | (rw [toSmt_un (op := UserOp.str_rev) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x)
            = SmtTerm.str_rev (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          obtain rfl := Option.some.inj h
          exact rev_sound _)
       | (rw [toSmt_un (op := UserOp.str_to_lower) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) x)
            = SmtTerm.str_to_lower (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          obtain rfl := Option.some.inj h
          exact lower_sound _)
       | (rw [toSmt_un (op := UserOp.str_to_upper) rfl hs, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) x)
            = SmtTerm.str_to_upper (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
          simp only; rw [← Node.toSmt, h0]
          obtain rfl := Option.some.inj h
          exact upper_sound _))
    | (have hs : cs.size = 3 := by simpa using hlen
       rw [toList_three hs] at hv
       obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h1, hv⟩ := List.forall₂_cons.1 hv
       obtain ⟨h2, -⟩ := List.forall₂_cons.1 hv
       rw [toSmt_tern (op := UserOp.str_substr) rfl hs, show ∀ x y z,
           __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
             = SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) from fun _ _ _ => rfl,
         __smtx_model_eval.eq_def]
       simp only; rw [← Node.toSmt, ← Node.toSmt, ← Node.toSmt, h0, h1, h2]
       obtain rfl := Option.some.inj h
       exact extract_sound _ _ _)

theorem combine_sound (M : Model) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : Vals M env cs.toList vs) (h : Model.combine k cs vs = some r) :
    __smtx_model_eval (toSmtModelE M env) (Node.app (.kind k) cs).toSmt = toVal r :=
  combine_sound_in _ hv h

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

theorem eval_pairs (M : Model) (T : Term) (s : SmtTerm) (sv : MVal)
    (hs : __smtx_model_eval (toSmtModelE M env) s = toVal sv) (hsr : sv.isRe = false) : ∀ (xs : List Term) (vs : List MVal),
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModelE M env) (__eo_to_smt x) = toVal v) xs vs →
    __smtx_model_eval (toSmtModelE M env)
        (__eo_to_smt_distinct_pairs s (tl (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) xs)) =
      SmtValue.Boolean (vs.all fun w => !(sv.veq w))
  | [], [], .nil => by
    simp only [tl, eoRightAssocNil, __eo_to_smt_distinct_pairs]
    exact eval_true _
  | x :: xs, v :: vs, .cons hx hr => by
    simp only [tl, eoRightAssocNil, eoApp2, __eo_to_smt_distinct_pairs]
    rw [eval_and, eval_not', eval_eq', hs, hx, eval_eq_toVal _ _ hsr]
    have := eval_pairs M T s sv hs hsr xs vs hr
    simp only [tl] at this
    rw [this]
    cases hb : (sv.veq v) <;> simp [hb, __smtx_model_eval_not, __smtx_model_eval_and, native_and, native_not]

theorem eval_distinct (M : Model) (T : Term) : ∀ (xs : List Term) (vs : List MVal),
    List.Forall₂ (fun x v => __smtx_model_eval (toSmtModelE M env) (__eo_to_smt x) = toVal v) xs vs →
    vs.any (·.isRe) = false →
    __smtx_model_eval (toSmtModelE M env)
        (__eo_to_smt_distinct (tl (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) xs)) =
      SmtValue.Boolean (Model.distinctVals vs)
  | [], [], .nil, _ => by
    simp only [tl, eoRightAssocNil, __eo_to_smt_distinct]
    exact eval_true _
  | x :: xs, v :: vs, .cons hx hr, hnr => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hnr
    simp only [tl, eoRightAssocNil, eoApp2, __eo_to_smt_distinct]
    have hp := eval_pairs M T _ v hx hnr.1 xs vs hr
    have hd := eval_distinct M T xs vs hr hnr.2
    simp only [tl] at hp hd
    rw [eval_and, hp, hd]
    simp [Model.distinctVals, __smtx_model_eval_and, native_and]

/-- **A `distinct` has its value.** -/
theorem distinct_sound (M : Model) {cs : Array Node} {vs : List MVal}
    (hv : Vals M env cs.toList vs) (hty : Model.distinctTyped cs = true) (h2 : 2 ≤ vs.length)
    (hnr : vs.any (·.isRe) = false) :
    __smtx_model_eval (toSmtModelE M env) (Node.app (.kind .DISTINCT) cs).toSmt =
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
    exact eval_distinct M T _ _ (vals_map hv) hnr

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
  simp only [Op.eoShape, nodeEoShape, isFnSkolemTerm, Bool.false_eq_true, ↓reduceIte, AppShape.toEo, Arity.accepts, List.length_map, Array.length_toList,
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

/-- **An application of a function value has its value.** -/
theorem apply_sound {M : Model} {f a g : MVal} (h : M.apply f a = some g) :
    __smtx_model_eval_apply (toSmtModelE M env) (toVal f) (toVal a) = toVal g := by
  unfold Model.apply at h
  split at h
  · cases h
  rename_i hna
  split at h
  · rename_i fid dom rng
    split at h
    · rename_i t ht
      split at h
      · rename_i hty
        simp only [Bool.and_eq_true, beq_iff_eq] at hty
        obtain ⟨rfl, rfl⟩ := hty
        have e1 : __smtx_model_eval_apply (toSmtModelE M env) (toVal (.fn fid t.dom t.rng)) (toVal a) =
            native_eval_fun_apply (toSmtModelE M env) ((fid : ℝ) + 1) t.dom t.rng (toVal a) := by
          have hnv := toVal_ne_notValue a (by simpa using hna)
          simp only [toVal]
          generalize toVal a = w at hnv ⊢
          cases w <;> simp_all [__smtx_model_eval_apply]
        have hne : ((fid : ℝ) + 1) ≠ native_default_fun_id := by
          simp only [native_default_fun_id]; positivity
        have hex : ∃ k : ℕ, ((fid : ℝ) + 1) = (k : ℝ) + 1 := ⟨fid, rfl⟩
        have hc : ∀ p : (∃ k : ℕ, ((fid : ℝ) + 1) = (k : ℝ) + 1), Classical.choose p = fid := by
          intro hex
          have := Classical.choose_spec hex
          have h2 : ((Classical.choose hex : ℕ) : ℝ) = fid := by linarith
          exact_mod_cast h2
        have hp : (fun p : MVal × MVal => decide (toVal p.1 = toVal a)) = (fun p => p.1.veq a) := by
          funext p
          by_cases e : p.1.veq a = true
          · simp [e, (veq_iff _ _).1 e]
          · have : toVal p.1 ≠ toVal a := fun h => e ((veq_iff _ _).2 h)
            simp [e, this]
        rw [e1]
        simp only [native_eval_fun_apply, model_fun_lookup, toSmtModelE, tableFun]
        simp only [hne, hex, ↓reduceIte, ↓reduceDIte, hc, ht, and_self, hp]
        cases hf : t.entries.find? (·.1.veq a) with
        | none => simp only [hf] at h ⊢; cases h; rfl
        | some p => rcases p with ⟨_, w⟩; simp only [hf] at h ⊢; cases h; rfl
      · cases h
    · cases h
  · cases h

theorem applyAll_sound {M : Model} : ∀ (vs : List MVal) (ts : List SmtTerm) (h : SmtTerm) (f r : MVal),
    List.Forall₂ (fun t v => __smtx_model_eval (toSmtModelE M env) t = toVal v) ts vs →
    ((∃ s T, h = SmtTerm.UConst s T) ∨ ∃ a b, h = SmtTerm.Apply a b) →
    __smtx_model_eval (toSmtModelE M env) h = toVal f → M.applyAll f vs = some r → __smtx_model_eval (toSmtModelE M env) (ts.foldl SmtTerm.Apply h) = toVal r
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

/-! ### Datatypes -/

/-- A curried application of a datatype constructor. -/
inductive DHead : Term → Prop
  | dtcons (s : native_String) (d : DatatypeDecl) (i : native_Nat) : DHead (Term.DtCons s d i)
  | app {g : Term} (x : Term) : DHead g → DHead (Term.Apply g x)

omit [LogosFacts] in
theorem toSmt_apply_dhead {f : Term} (h : DHead f) (y : Term) :
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
theorem toSmt_foldl_dhead : ∀ (xs : List Term) {f : Term}, DHead f →
    __eo_to_smt (xs.foldl Term.Apply f) = (xs.map __eo_to_smt).foldl SmtTerm.Apply (__eo_to_smt f)
  | [], _, _ => rfl
  | x :: xs, f, hf => by
    simp only [List.foldl, List.map]
    rw [toSmt_foldl_dhead xs (DHead.app x hf), toSmt_apply_dhead hf]

omit [LogosFacts] in
/-- A constructor that has a Logos term is a `Term.DtCons`. -/
theorem dtCons_toEo {T : TypeNode} {i : Nat} {c : native_String × SmtDatatypeDecl × Nat}
    (h : Model.consOf? (Node.const (.dtCons T i)) = some c) :
    ∃ a d, (Node.const (.dtCons T i)).toEo = Term.DtCons a d i := by
  by_cases hd : ∃ s d, T = .datatype s d
  · obtain ⟨s, d, rfl⟩ := hd
    exact ⟨_, _, by simp only [Node.toEo, Const.toEo]; rfl⟩
  · exfalso
    have e : (Node.const (.dtCons T i)).toEo = Term.Stuck := by
      cases T <;> simp_all [Node.toEo, Const.toEo]
    have e2 : (Node.const (.dtCons T i)).toSmt = SmtTerm.None := by
      unfold Node.toSmt; rw [e]; rfl
    simp [Model.consOf?, e2] at h

omit [LogosFacts] in
/-- A selector that has a Logos term is a `Term.DtSel`. -/
theorem dtSel_toEo {T : TypeNode} {i j : Nat} {c : native_String × SmtDatatypeDecl × Nat × Nat}
    (h : Model.selOf? (Node.const (.dtSel T i j)) = some c) :
    ∃ a d, (Node.const (.dtSel T i j)).toEo = Term.DtSel a d i j := by
  by_cases hd : ∃ s d, T = .datatype s d
  · obtain ⟨s, d, rfl⟩ := hd
    exact ⟨_, _, by simp only [Node.toEo, Const.toEo]; rfl⟩
  · exfalso
    have e : (Node.const (.dtSel T i j)).toEo = Term.Stuck := by
      cases T <;> simp_all [Node.toEo, Const.toEo]
    have e2 : (Node.const (.dtSel T i j)).toSmt = SmtTerm.None := by
      unfold Node.toSmt; rw [e]; rfl
    simp [Model.selOf?, e2] at h

omit [LogosFacts] in
theorem toSmt_cons (f : Node) (cs : Array Node) (hf : DHead f.toEo) :
    (Node.app (.node .APPLY_CONSTRUCTOR f) cs).toSmt = (cs.toList.map Node.toSmt).foldl SmtTerm.Apply f.toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp only [Op.eoShape, nodeEoShape, isFnSkolemTerm, Bool.false_eq_true, ↓reduceIte, AppShape.toEo, Arity.accepts, List.length_map, Array.length_toList,
    Nat.zero_le, decide_true, ↓reduceIte]
  rw [toSmt_foldl_dhead _ hf, List.map_map]
  rfl

omit [LogosFacts] in
theorem toSmt_tester (f x : Node) (cs : Array Node) (hcs : cs.toList = [x]) :
    (Node.app (.node .APPLY_TESTER f) cs).toSmt = SmtTerm.Apply (__eo_to_smt_tester f.toSmt) x.toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp only [Op.eoShape, nodeEoShape, isFnSkolemTerm, Bool.false_eq_true, ↓reduceIte, AppShape.toEo, Arity.accepts, hcs,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte, List.foldl]
  rfl

omit [LogosFacts] in
theorem toSmt_selector (f x : Node) (cs : Array Node) (hcs : cs.toList = [x]) {a : native_String} {d : DatatypeDecl}
    {i j : Nat} (hf : f.toEo = Term.DtSel a d i j) :
    (Node.app (.node .APPLY_SELECTOR f) cs).toSmt = SmtTerm.Apply f.toSmt x.toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp only [Op.eoShape, nodeEoShape, isFnSkolemTerm, Bool.false_eq_true, ↓reduceIte, AppShape.toEo, Arity.accepts, hcs,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte, List.foldl, hf]
  rfl

theorem toVal_head (v : MVal) : __smtx_apply_head_value (toVal v) = toVal v.head := by
  induction v with
  | app f a ihf _ => simp only [toVal, __smtx_apply_head_value, MVal.head, ihf]
  | sins e s =>
    rcases toVal_set_shape (.sins e s) rfl with ⟨m, hm⟩ | hm <;> simp only [MVal.head, hm, __smtx_apply_head_value]
  | str w => simp [toVal, MVal.head, __smtx_apply_head_value]
  | _ => rfl

omit [LogosFacts] in
/-- Booleans are compared as Booleans. -/
@[simp] theorem veq_bool (a b : Bool) : (MVal.bool a).veq (.bool b) = (a == b) := by
  rw [MVal.veq.eq_def]; simp [MVal.isSet]

/-- Comparing with a constructor is structural. -/
theorem veq_dtc (v : MVal) (s : native_String) (dd : SmtDatatypeDecl) (i : Nat) :
    v.veq (.dtc s dd i) = (v == .dtc s dd i) := by
  rw [MVal.veq.eq_def]
  cases v <;> simp [MVal.isSet]

theorem veq_toVal (a b : MVal) : native_veq (toVal a) (toVal b) = a.veq b := by
  by_cases h : a.veq b = true
  · simp [native_veq, (veq_iff a b).1 h, h]
  · have : toVal a ≠ toVal b := fun e => h ((veq_iff a b).2 e)
    simp [native_veq, this, h]

omit [LogosFacts] in
theorem toVal_argNth : ∀ (v : MVal) (n npos : Nat) {w : MVal}, v.argNth n npos = some w →
    __smtx_apply_arg_nth_value (toVal v) n npos = toVal w
  | .app f a, n, k + 1, w, h => by
    simp only [MVal.argNth] at h
    simp only [toVal, __smtx_apply_arg_nth_value, native_ite, native_nateq]
    by_cases e : n = k
    · subst e; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h; simp
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      have : (n == k) = false := by simpa using e
      rw [this] at h
      exact toVal_argNth f n k h
  | .app _ _, _, 0, _, h => by simp [MVal.argNth] at h
  | .bool _, _, _, _, h | .uval .., _, _, _, h | .fn .., _, _, _, h | .dtc .., _, _, _, h => by
    simp [MVal.argNth] at h

theorem eval_apply_cons_toVal (M : SmtModel) (hv a : MVal)
    (h : (∃ s dd i, hv = .dtc s dd i) ∨ ∃ f x, hv = .app f x) (ha : a.notValue = false) :
    __smtx_model_eval_apply M (toVal hv) (toVal a) = SmtValue.Apply (toVal hv) (toVal a) := by
  have hnv := toVal_ne_notValue a ha
  generalize toVal a = w at hnv ⊢
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases w <;> simp_all [toVal, __smtx_model_eval_apply]

/-- **A constructor applied to arguments has its value.** -/
theorem eval_chain (M : Model) : ∀ (vs : List MVal) (ts : List SmtTerm) (h : SmtTerm) (hv : MVal),
    List.Forall₂ (fun t v => __smtx_model_eval (toSmtModelE M env) t = toVal v) ts vs →
    ((∃ s dd i, h = SmtTerm.DtCons s dd i) ∨ ∃ a b, h = SmtTerm.Apply a b) →
    ((∃ s dd i, hv = .dtc s dd i) ∨ ∃ f x, hv = .app f x) →
    __smtx_model_eval (toSmtModelE M env) h = toVal hv → (∀ v ∈ vs, v.notValue = false) →
    __smtx_model_eval (toSmtModelE M env) (ts.foldl SmtTerm.Apply h) = toVal (vs.foldl .app hv)
  | [], [], _, _, .nil, _, _, hh, _ => hh
  | v :: vs, t :: ts, h, hv, .cons ht hr, hs, hvs, hh, hna => by
    simp only [List.foldl]
    refine eval_chain M vs ts _ _ hr (Or.inr ⟨_, _, rfl⟩) (Or.inr ⟨_, _, rfl⟩) ?_
      (fun w hw => hna w (List.mem_cons_of_mem _ hw))
    have e : __smtx_model_eval (toSmtModelE M env) (SmtTerm.Apply h t) =
        __smtx_model_eval_apply (toSmtModelE M env) (__smtx_model_eval (toSmtModelE M env) h)
          (__smtx_model_eval (toSmtModelE M env) t) := by
      rcases hs with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rw [__smtx_model_eval.eq_def]
    rw [e, hh, ht, eval_apply_cons_toVal _ _ _ hvs (hna v (List.mem_cons_self ..))]
    rfl

omit [LogosFacts] in
theorem lookup_sound {M : Model} {x : native_String} {T : SmtType} {v : MVal} (h : M.lookup x T = some v) :
    native_model_lookup (toSmtModelE M env) x T = toVal v := by
  simp only [native_model_lookup, model_key, toSmtModelE, Bool.false_eq_true, ↓reduceIte, h]

omit [LogosFacts] in
theorem wrongSelName_eq (i j : Nat) : Model.wrongSelName i j = native_wrong_apply_sel_id i j := rfl

/-! ### The evaluation -/

omit [LogosFacts] in
theorem divByZeroName_eq : Model.divByZeroName = native_div_by_zero_id := rfl
omit [LogosFacts] in
theorem modByZeroName_eq : Model.modByZeroName = native_mod_by_zero_id := rfl
omit [LogosFacts] in
theorem qdivByZeroName_eq : Model.qdivByZeroName = native_qdiv_by_zero_id := rfl

/-- **Integer division and modulus, and division by zero, are Logos's**
(`Model.divMod?`): by a nonzero integer, Logos's total operations; by zero,
the model's function of division by zero applied to the dividend. -/
theorem divMod_sound (M : Model) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : Vals M env cs.toList vs) (h : M.divMod? k vs = some (some r)) :
    __smtx_model_eval (toSmtModelE M env) (Node.app (.kind k) cs).toSmt = toVal r := by
  have hlen : cs.size = vs.length := by simpa using hv.length_eq
  unfold Model.divMod? at h
  split at h
  · -- `div`
    rename_i a b
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_bin (op := UserOp.div) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y)
      = SmtTerm.div (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
    simp only [Option.some.injEq] at h
    split at h
    · rename_i hb
      obtain ⟨fv, hl, ha⟩ := Option.bind_eq_some_iff.1 h
      have hb' : b = 0 := by simpa using hb
      subst hb'
      simp only [toVal, __smtx_model_eval_eq, native_veq, decide_true, __smtx_model_eval_ite]
      rw [← divByZeroName_eq, lookup_sound hl]
      exact apply_sound ha
    · rename_i hb
      have hb' : b ≠ 0 := by simpa using hb
      cases h
      simp [toVal, __smtx_model_eval_eq, native_veq, hb', __smtx_model_eval_ite,
        __smtx_model_eval_div_total]
  · -- `mod`
    rename_i a b
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_bin (op := UserOp.mod) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y)
      = SmtTerm.mod (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
    simp only [Option.some.injEq] at h
    split at h
    · rename_i hb
      obtain ⟨fv, hl, ha⟩ := Option.bind_eq_some_iff.1 h
      have hb' : b = 0 := by simpa using hb
      subst hb'
      simp only [toVal, __smtx_model_eval_eq, native_veq, decide_true, __smtx_model_eval_ite]
      rw [← modByZeroName_eq, lookup_sound hl]
      exact apply_sound ha
    · rename_i hb
      have hb' : b ≠ 0 := by simpa using hb
      cases h
      simp [toVal, __smtx_model_eval_eq, native_veq, hb', __smtx_model_eval_ite,
        __smtx_model_eval_mod_total]
  · -- `div_total`
    rename_i a b
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_bin (op := UserOp.div_total) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y)
      = SmtTerm.div_total (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
    simp only [Option.some.injEq] at h
    cases h
    rfl
  · -- `mod_total`
    rename_i a b
    have hs : cs.size = 2 := by simpa using hlen
    rw [toList_two hs] at hv
    obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
    obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
    rw [toSmt_bin (op := UserOp.mod_total) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y)
      = SmtTerm.mod_total (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
    simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
    simp only [Option.some.injEq] at h
    cases h
    rfl
  · -- `/` by zero
    rename_i a b
    split at h
    · rename_i hb
      have hs : cs.size = 2 := by simpa using hlen
      rw [toList_two hs] at hv
      obtain ⟨h0, hv⟩ := List.forall₂_cons.1 hv
      obtain ⟨h1, -⟩ := List.forall₂_cons.1 hv
      rw [toSmt_bin (op := UserOp.qdiv) rfl hs, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)
        = SmtTerm.qdiv (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
      simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]
      simp only [Option.some.injEq] at h
      obtain ⟨fv, hl, ha⟩ := Option.bind_eq_some_iff.1 h
      have hb' : b = 0 := by simpa using hb
      subst hb'
      simp only [toVal, __smtx_to_real_coerce, __smtx_model_eval_eq, native_veq, native_mk_real,
        __smtx_model_eval_ite]
      simp only [Rat.cast_zero, Int.cast_zero, Int.cast_one, zero_div, decide_true]
      rw [← qdivByZeroName_eq, lookup_sound hl]
      exact apply_sound ha
    · cases h
  · cases h


/-- The evaluation at fuel `n` is sound. -/
def EvOk (M : Model) (n : Nat) : Prop :=
  ∀ env t S, MemoOk M env S → MemoOk M env (M.ev env n t S).2 ∧ ∀ v, (M.ev env n t S).1 = some v → __smtx_model_eval (toSmtModelE M env) t.toSmt = toVal v

omit [LogosFacts] in
theorem evList_sound (M : Model) (n : Nat) (IH : EvOk M n) : ∀ (l : List Node) (S : Model.Memo),
    MemoOk M env S → MemoOk M env (M.evList env n l S).2 ∧ ∀ vs, (M.evList env n l S).1 = some vs → Vals M env l vs
  | [], S, hS => by
    rw [Model.evList]
    exact ⟨hS, fun vs h => by cases h; exact .nil⟩
  | c :: cs, S, hS => by
    rw [Model.evList]
    obtain ⟨hS1, hv1⟩ := IH env c S hS
    rcases e1 : M.ev env n c S with ⟨r1, S1⟩
    rw [e1] at hS1 hv1
    try dsimp only
    cases r1 with
    | none => exact ⟨hS1, fun vs h => by cases h⟩
    | some v =>
      dsimp only
      obtain ⟨hS2, hv2⟩ := evList_sound M n IH cs S1 hS1
      rcases e2 : M.evList env n cs S1 with ⟨r2, S2⟩
      rw [e2] at hS2 hv2
      try dsimp only
      cases r2 with
      | none => exact ⟨hS2, fun vs h => by cases h⟩
      | some vs => exact ⟨hS2, fun vs' h => by cases h; exact .cons (hv1 v rfl) (hv2 vs rfl)⟩

omit [LogosFacts] in
theorem mem_dedupVals {v : MVal} : ∀ {l : List MVal}, v ∈ Model.dedupVals l → v ∈ l
  | [], h => by simp [Model.dedupVals] at h
  | w :: ws, h => by
    simp only [Model.dedupVals] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dedupVals h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_dedupVals h)

omit [LogosFacts] in
theorem candidates_ty {M : Model} {T : SmtType} {v : MVal} (h : v ∈ M.candidates T) : v.ty = T := by
  unfold Model.candidates at h
  have := List.mem_filter.1 (mem_dedupVals h)
  simpa using this.2

omit [LogosFacts] in
/-- The Logos translation of a chain of `exists` binders. -/
theorem eval_exists_cons (N : SmtModel) (s : native_String) (T : SmtType) (b : SmtTerm) (w : SmtValue)
    (hty : __smtx_typeof_value w = T) (hc : __smtx_value_canonical N.usortDom w = true)
    (hb : __smtx_model_eval (native_model_push N s T w) b = SmtValue.Boolean true) :
    __smtx_model_eval N (SmtTerm.exists s T b) = SmtValue.Boolean true := by
  rw [__smtx_model_eval.eq_def]
  simp only
  split
  · rfl
  · rename_i hn; exact absurd ⟨w, hty, hc, hb⟩ hn

/-- The goal of the witnesses: the body, or its negation. -/
def witnessGoal (pol : Bool) (body : Node) : SmtTerm := if pol then body.toSmt else SmtTerm.not body.toSmt

theorem witness_sound (M : Model) (n : Nat) (IH : EvOk M n) (pol : Bool) (body : Node) :
    ∀ (vs : List Node) (env env' : Model.Env), M.witness env n pol body vs = some env' →
      __smtx_model_eval (toSmtModelE M env)
        (__eo_to_smt_exists (eoList (vs.map Node.toEo)) (witnessGoal pol body)) = SmtValue.Boolean true
  | [], env, env', h => by
    unfold Model.witness at h
    obtain ⟨-, hv⟩ := IH env body {} (memoOk_empty M env)
    rcases e : (M.ev env n body {}).1 with _ | r
    · rw [e] at h; cases h
    · rw [e] at h
      cases r with
      | bool b =>
        dsimp only at h
        split at h
        · rename_i hb
          have hb : b = pol := by simpa using hb
          subst hb
          have hev := hv _ e
          simp only [List.map_nil, eoList, __eo_to_smt_exists, witnessGoal]
          cases b with
          | true => simpa [toVal] using hev
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [__smtx_model_eval.eq_def]
            simp only
            rw [hev]; rfl
        · cases h
      | _ => cases h
  | .boundVar x T :: rest, env, env', h => by
    unfold Model.witness at h
    obtain ⟨v, hmem, hw⟩ := List.exists_of_findSome?_eq_some h
    have ih := witness_sound M n IH pol body rest _ _ hw
    rw [← toSmtModelE_push] at ih
    simp only [List.map_cons, eoList]
    rw [show (Node.boundVar x T).toEo = Term.Var (Term.String (native_string_lit x)) T.toEo by rw [Node.toEo]]
    simp only [__eo_to_smt_exists]
    exact eval_exists_cons _ _ _ _ _ (by rw [typeof_toVal]; exact candidates_ty hmem)
      (canonical_toVal v) ih
  | .const _ :: _, _, _, h | .var .. :: _, _, _, h | .skolem .. :: _, _, _, h | .app .. :: _, _, _, h => by
    unfold Model.witness at h; cases h

theorem quant_sound (M : Model) (n : Nat) (IH : EvOk M n) (k : Kind) (cs : Array Node) (v : MVal)
    (hk : (k == .FORALL || k == .EXISTS) = true) (h : M.quant env n (k == .EXISTS) cs = some v) :
    __smtx_model_eval (toSmtModelE M env) (Node.app (.kind k) cs).toSmt = toVal v := by
  unfold Model.quant at h
  split at h
  · rename_i vs body hcs
    split at h
    · rename_i hif
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_iff_exists] at hif
      obtain ⟨hne, env', hw⟩ := hif
      have ih := witness_sound M n IH _ body vs.toList env env' hw
      obtain ⟨a, rest, hvs⟩ : ∃ a rest, vs.toList = a :: rest := by
        cases e : vs.toList with
        | nil =>
          have : vs = #[] := Array.toList_eq_nil_iff.1 e
          subst this; simp at hne
        | cons a rest => exact ⟨a, rest, rfl⟩
      have hbvl : (Node.app (.kind .BOUND_VAR_LIST) vs).toEo = eoList (vs.toList.map Node.toEo) := by
        rw [Node.toEo_app]; rfl
      unfold Node.toSmt at ih ⊢
      rw [Node.toEo_app, hcs]
      simp only [List.map_cons, List.map_nil]
      rw [hbvl]
      rw [hvs] at ih ⊢
      simp only [List.map_cons, eoList] at ih ⊢
      simp only [Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with rfl | rfl
      · show __smtx_model_eval _ (__eo_to_smt (eoApp2 UserOp.forall _ _)) = _
        simp only [eoApp2, __eo_to_smt]
        rw [__smtx_model_eval.eq_def]
        simp only [witnessGoal, show (Kind.FORALL == Kind.EXISTS) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, Node.toSmt] at ih
        simp only
        rw [ih]; rfl
      · show __smtx_model_eval _ (__eo_to_smt (eoApp2 UserOp.exists _ _)) = _
        simp only [eoApp2, __eo_to_smt]
        simp only [witnessGoal, show (Kind.EXISTS == Kind.EXISTS) = true from rfl, ↓reduceIte,
          Node.toSmt] at ih
        rw [ih]; rfl
    · cases h
  · cases h

theorem evNode_sound (M : Model) (n : Nat) (IH : EvOk M n) (t : Node) (S : Model.Memo) (hS : MemoOk M env S) :
    MemoOk M env (M.evNode env n t S).2 ∧ ∀ v, (M.evNode env n t S).1 = some v → __smtx_model_eval (toSmtModelE M env) t.toSmt = toVal v := by
  unfold Model.evNode
  split
  · rename_i b
    exact ⟨hS, fun v h => by cases h; exact evalsTo_const _ b⟩
  · rename_i i
    exact ⟨hS, fun v h => by
      cases h; simpa [Node.toSmt, Node.toEo, Const.toEo, toVal] using eval_numeral_term (toSmtModelE M env) i⟩
  · rename_i q
    exact ⟨hS, fun v h => by
      cases h; simpa [Node.toSmt, Node.toEo, Const.toEo, toVal, native_rat_to_real] using
        eval_rational_term (toSmtModelE M env) q⟩
  · rename_i w
    refine ⟨hS, fun v h => ?_⟩
    dsimp only at h
    split at h
    · rename_i hw
      cases h
      have hid : w.map MVal.clampChar = w := by
        rw [List.all_eq_true] at hw
        conv_rhs => rw [← List.map_id w]
        apply List.map_congr_left
        intro c hc
        have := hw c hc
        simp only [decide_eq_true_eq] at this
        simp [MVal.clampChar, this]
      have e : (Node.const (.string w)).toSmt = SmtTerm.String w := by
        simp only [Node.toSmt, Node.toEo, Const.toEo]
        rfl
      rw [e, __smtx_model_eval.eq_def]
      simp only [toVal, hid]
    · cases h
  · rename_i T
    refine ⟨hS, fun v h => ?_⟩
    dsimp only at h
    split at h
    · cases h
    · rename_i hT
      cases h
      have hT' : tyS T ≠ SmtType.None := by simpa using hT
      have e : (Node.const (.emptySet T)).toSmt = SmtTerm.set_empty (tyS T) := by
        simp only [Node.toSmt, Node.toEo, Const.toEo]
        rw [show (TypeNode.set T).toEo = Term.Apply (Term.UOp UserOp.Set) T.toEo from rfl]
        simp only [__eo_to_smt, __eo_to_smt_type]
        simp only [tyS] at hT'
        simp [__smtx_typeof_guard, native_ite, native_Teq, hT', __eo_to_smt_set_empty, tyS]
      rw [e, __smtx_model_eval.eq_def]
      rfl
  · exact ⟨hS, fun v h => eval_var h⟩
  · exact ⟨hS, fun v h => eval_boundVar h⟩
  · rename_i cs
    split
    · rename_i hty
      obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
      rcases e1 : M.evList env n cs.toList S with ⟨r1, S1⟩
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
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h2
          exact distinct_sound M (hv1 vs rfl) hty h2.1 h2.2
        · cases h
    · exact ⟨hS, fun v h => by cases h⟩
  · rename_i k cs _
    split
    · rename_i hk
      exact ⟨hS, fun v h => quant_sound M n IH k cs v hk h⟩
    obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
    rcases e1 : M.evList env n cs.toList S with ⟨r1, S1⟩
    rw [e1] at hS1 hv1
    try dsimp only
    cases r1 with
    | none => exact ⟨hS1, fun v h => by cases h⟩
    | some vs =>
      refine ⟨hS1, fun v h => ?_⟩
      dsimp only at h
      cases hd : M.divMod? k vs with
      | none =>
        rw [hd] at h
        exact combine_sound M (hv1 vs rfl) h
      | some o =>
        rw [hd] at h
        simp only [Option.getD_some] at h
        exact divMod_sound M (hv1 vs rfl) (by rw [hd, h])
  · rename_i k is cs
    obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
    rcases e1 : M.evList env n cs.toList S with ⟨r1, S1⟩
    rw [e1] at hS1 hv1
    try dsimp only
    cases r1 with
    | none => exact ⟨hS1, fun v h => by cases h⟩
    | some vs => exact ⟨hS1, fun v h => combineIdx_sound_in _ (hv1 vs rfl) h⟩
  · rename_i f T cs
    cases hf : M.const f T with
    | none => exact ⟨hS, fun v h => by cases h⟩
    | some fv =>
      dsimp only
      obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
      rcases e1 : M.evList env n cs.toList S with ⟨r1, S1⟩
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
  · -- a constructor applied
    rename_i _ T idx cs
    split
    · exact ⟨hS, fun v h => by cases h⟩
    · rename_i sc ddc ic hc
      obtain ⟨a, d, he⟩ := dtCons_toEo hc
      have hsmt : (Node.const (.dtCons T idx)).toSmt = SmtTerm.DtCons sc ddc ic := by
        simp only [Model.consOf?] at hc; split at hc <;> simp_all
      obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
      rcases e1 : M.evList env n cs.toList S with ⟨r1, S1⟩
      rw [e1] at hS1 hv1
      try dsimp only
      cases r1 with
      | none => exact ⟨hS1, fun v h => by cases h⟩
      | some vs =>
        refine ⟨hS1, fun v h => ?_⟩
        dsimp only at h
        split at h
        · cases h
        rename_i hna
        cases h
        rw [toSmt_cons _ cs (he ▸ DHead.dtcons a d idx), hsmt]
        refine eval_chain M vs _ _ _ ((List.forall₂_map_left_iff).2 (hv1 vs rfl))
          (Or.inl ⟨_, _, _, rfl⟩) (Or.inl ⟨_, _, _, rfl⟩) ?_ ?_
        · rw [__smtx_model_eval.eq_def]; rfl
        · intro w hw
          simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hna
          exact hna w hw
  · -- a tester applied
    rename_i _ T idx cs
    split
    · rename_i sc ddc ic x hc hcs
      have hsmt : (Node.const (.dtCons T idx)).toSmt = SmtTerm.DtCons sc ddc ic := by
        simp only [Model.consOf?] at hc; split at hc <;> simp_all
      obtain ⟨hS1, hv1⟩ := IH env x S hS
      rcases e1 : M.ev env n x S with ⟨r1, S1⟩
      rw [e1] at hS1 hv1
      try dsimp only
      cases r1 with
      | none => exact ⟨hS1, fun v h => by cases h⟩
      | some w =>
        refine ⟨hS1, fun v h => ?_⟩
        cases h
        rw [toSmt_tester _ x cs hcs, hsmt]
        show __smtx_model_eval _ (SmtTerm.Apply (SmtTerm.DtTester sc ddc ic) _) = _
        rw [__smtx_model_eval.eq_def]
        simp only [__smtx_model_eval_dt_tester, hv1 w rfl, toVal_head]
        rw [show SmtValue.DtCons sc ddc ic = toVal (.dtc sc ddc ic) from rfl, veq_toVal, veq_dtc]
        rfl
    · exact ⟨hS, fun v h => by cases h⟩
  · -- a selector applied
    rename_i _ T idx jdx cs
    split
    · rename_i sc ddc ic jc x hc hcs
      obtain ⟨a, d, he⟩ := dtSel_toEo hc
      have hsmt : (Node.const (.dtSel T idx jdx)).toSmt = SmtTerm.DtSel sc ddc ic jc := by
        simp only [Model.selOf?] at hc; split at hc <;> simp_all
      obtain ⟨hS1, hv1⟩ := IH env x S hS
      rcases e1 : M.ev env n x S with ⟨r1, S1⟩
      rw [e1] at hS1 hv1
      try dsimp only
      cases r1 with
      | none => exact ⟨hS1, fun v h => by cases h⟩
      | some w =>
        refine ⟨hS1, fun v h => ?_⟩
        dsimp only at h
        rw [toSmt_selector _ x cs hcs he, hsmt]
        rw [__smtx_model_eval.eq_def]
        simp only [__smtx_model_eval_dt_sel, hv1 w rfl, toVal_head, native_ite]
        rw [show SmtValue.DtCons sc ddc ic = toVal (.dtc sc ddc ic) from rfl, veq_toVal, veq_dtc]
        split at h
        · rename_i hh
          simp only [hh, ↓reduceIte]
          exact toVal_argNth _ _ _ h
        · rename_i hh
          simp only [hh, Bool.false_eq_true, ↓reduceIte]
          cases hl : M.lookup (Model.wrongSelName ic jc) (Model.wrongSelType sc ddc ic jc) with
          | none => simp [hl] at h
          | some fv =>
            simp only [hl, Option.bind_some] at h
            rw [← wrongSelName_eq, show SmtType.FunType (SmtType.Datatype sc ddc) (__smtx_ret_typeof_sel sc ddc ic jc)
              = Model.wrongSelType sc ddc ic jc from rfl, lookup_sound hl]
            exact apply_sound h
    · exact ⟨hS, fun v h => by cases h⟩
  · -- a nullary constructor
    rename_i T idx
    refine ⟨hS, fun v h => ?_⟩
    cases hc : Model.consOf? (Node.const (.dtCons T idx)) with
    | none => simp [hc] at h
    | some c =>
      rcases c with ⟨sc, ddc, ic⟩
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst h
      have hsmt : (Node.const (.dtCons T idx)).toSmt = SmtTerm.DtCons sc ddc ic := by
        simp only [Model.consOf?] at hc; split at hc <;> simp_all
      rw [hsmt, __smtx_model_eval.eq_def]; rfl
  · exact ⟨hS, fun v h => by cases h⟩

/-- **The evaluation is sound**, at every fuel. -/
theorem ev_sound (M : Model) : ∀ n, EvOk M n
  | 0 => fun env t S hS => by
    rw [Model.ev]
    exact ⟨hS, fun v h => by cases h⟩
  | n + 1 => fun env t S hS => by
    rw [Model.ev]
    split
    · rename_i w hw
      exact ⟨hS, fun v h => hS t v (by dsimp only at h; rw [hw, h])⟩
    · obtain ⟨hS1, hv1⟩ := evNode_sound M n (ev_sound M n) t S hS
      rcases e1 : M.evNode env n t S with ⟨r, S1⟩
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
theorem vals_true {M : Model} : ∀ {l : List Node} {vs : List MVal}, Vals M [] l vs →
    (∀ v ∈ vs, v = .bool true) → ∀ a ∈ l, __smtx_model_eval (toSmtModel M) a.toSmt = SmtValue.Boolean true
  | _, _, .nil, _ => by simp
  | _, _, .cons h hr, hv => by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := hv _ (List.mem_cons.2 (Or.inl rfl))
      rw [← toSmtModelE_nil, h, hb]; rfl
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
  obtain ⟨-, hv⟩ := evList_sound M Model.fuel (ev_sound M _) as {} (memoOk_empty M [])
  rcases e : M.evList [] Model.fuel as {} with ⟨r, S⟩
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
theorem solveScript_sat (sc : Script) (u : UserOptions) (ee pp wp co vs te ev : Bool)
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co vs te ev = .ok (out, r))
    (hs : r.answer = .sat) {opts : PPOptions} {as : List Node}
    (hin : ppInput sc u = .ok (opts, as)) :
    ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
  simp only [solveScript, hin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · -- whichever solved it, the answer is `sat` only if the model satisfies the
    -- input
    have key : ∀ (o : NodeOrder) (r0 : Solver.Result) (w : Solver.Unknown), (if r0.answer != .sat then r0 else
        if (Solver.buildModel r0.ee (Solver.relevantTerms r0.asserted) (Solver.freeConsts as)
            (engineDefs as opts pp o) as r0.arithModel r0.asserted).satisfies as then
          { r0 with model := some (Solver.buildModel r0.ee (Solver.relevantTerms r0.asserted)
            (Solver.freeConsts as) (engineDefs as opts pp o) as r0.arithModel r0.asserted) }
        else rejectModel r0 w).answer = .sat →
        ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
      intro _ r0 _ hs
      split at hs
      · rename_i hne
        simp [hs] at hne
      · split at hs
        · rename_i hsat
          exact ⟨_, Solver.satisfies_sound hsat⟩
        · rw [rejectModel_answer] at hs
          cases hs
    split at h
    · try simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact key _ _ _ hs
    · split at h
      · simp at h
      · try simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact key _ _ _ hs

end Telos.Frontend
