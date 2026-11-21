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
  | .dtc s dd i => .DtCons s dd i
  | .app f a => .Apply (toVal f) (toVal a)
  | .int i => .Numeral i
  | .rat q => .Real (q : ℝ)

omit [LogosFacts] in
theorem toVal_inj {a b : MVal} (h : toVal a = toVal b) : a = b := by
  induction a generalizing b with
  | app f a ihf iha =>
    cases b <;> simp only [toVal, reduceCtorEq, SmtValue.Apply.injEq] at h
    rw [ihf h.1, iha h.2]
  | _ => cases b <;> simp_all [toVal]

omit [LogosFacts] in
theorem typeof_toVal (v : MVal) : __smtx_typeof_value (toVal v) = v.ty := by
  induction v with
  | app f a ihf iha => simp only [toVal, MVal.ty, __smtx_typeof_value, ihf, iha]
  | dtc => rfl
  | _ => simp [toVal, MVal.ty, __smtx_typeof_value]

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

omit [LogosFacts] in
theorem usort_dom_wf_univ : usort_dom_wf (fun _ => (Set.univ : Set ModelId)) := by
  intro i
  refine ⟨Set.mem_univ _, fun _ n => ⟨(n : ℝ), Set.mem_univ _, ?_⟩⟩
  simp

omit [LogosFacts] in
theorem canonical_toVal (v : MVal) :
    __smtx_value_canonical (fun _ => (Set.univ : Set ModelId)) (toVal v) = true := by
  induction v with
  | app f a ihf iha => simp only [toVal, __smtx_value_canonical, ihf, iha, native_and, Bool.and_self]
  | _ => simp [toVal, __smtx_value_canonical, native_usort_mem]

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
  simp only [native_model_lookup, model_key, toSmtModel, Bool.false_eq_true, ↓reduceIte, h]

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
abbrev ValsIn (N : SmtModel) (l : List Node) (vs : List MVal) : Prop :=
  List.Forall₂ (fun c v => __smtx_model_eval N c.toSmt = toVal v) l vs

abbrev Vals (M : Model) (l : List Node) (vs : List MVal) : Prop := ValsIn (toSmtModel M) l vs

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
    (h : Model.chainNil k (__smtx_typeof x.toSmt) = some nv) :
    __smtx_model_eval N (__eo_to_smt (typedNil op x.toEo)) = toVal nv := by
  unfold typedNil
  have hx : __eo_to_smt x.toEo = x.toSmt := rfl
  rw [hx]
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · revert h
    cases __smtx_typeof x.toSmt <;> simp only [Model.chainNil, reduceCtorEq, false_implies, Option.some.injEq] <;>
      intro h <;> subst h <;>
      simp [typedNilOfType, eval_numeral_term, eval_rational_term, toVal, native_rat_to_real, native_mk_rational]

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
/-- **A connective has its value.** -/
theorem combine_sound_in (N : SmtModel) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : ValsIn N cs.toList vs) (h : Model.combine k cs vs = some r) :
    __smtx_model_eval N (Node.app (.kind k) cs).toSmt = toVal r := by
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
          simp only; rw [← Node.toSmt, ← Node.toSmt, h0, h1]; exact leqV_sound h))
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
          simp [toVal, __smtx_model_eval_to_real, native_int_to_real, Rat.cast_intCast]))

omit [LogosFacts] in
theorem combine_sound (M : Model) {k : Kind} {cs : Array Node} {vs : List MVal} {r : MVal}
    (hv : Vals M cs.toList vs) (h : Model.combine k cs vs = some r) :
    __smtx_model_eval (toSmtModel M) (Node.app (.kind k) cs).toSmt = toVal r :=
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
  simp only [Op.eoShape, nodeEoShape, AppShape.toEo, Arity.accepts, List.length_map, Array.length_toList,
    Nat.zero_le, decide_true, ↓reduceIte]
  rw [toSmt_foldl_dhead _ hf, List.map_map]
  rfl

omit [LogosFacts] in
theorem toSmt_tester (f x : Node) (cs : Array Node) (hcs : cs.toList = [x]) :
    (Node.app (.node .APPLY_TESTER f) cs).toSmt = SmtTerm.Apply (__eo_to_smt_tester f.toSmt) x.toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp only [Op.eoShape, nodeEoShape, AppShape.toEo, Arity.accepts, hcs,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte, List.foldl]
  rfl

omit [LogosFacts] in
theorem toSmt_selector (f x : Node) (cs : Array Node) (hcs : cs.toList = [x]) {a : native_String} {d : DatatypeDecl}
    {i j : Nat} (hf : f.toEo = Term.DtSel a d i j) :
    (Node.app (.node .APPLY_SELECTOR f) cs).toSmt = SmtTerm.Apply f.toSmt x.toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp only [Op.eoShape, nodeEoShape, AppShape.toEo, Arity.accepts, hcs,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, beq_self_eq_true, ↓reduceIte, List.foldl, hf]
  rfl

omit [LogosFacts] in
theorem toVal_head (v : MVal) : __smtx_apply_head_value (toVal v) = toVal v.head := by
  induction v with
  | app f a ihf _ => simp only [toVal, __smtx_apply_head_value, MVal.head, ihf]
  | _ => rfl

omit [LogosFacts] in
theorem veq_toVal (a b : MVal) : native_veq (toVal a) (toVal b) = (a == b) := by
  simp only [native_veq]
  by_cases h : a = b
  · subst h; simp
  · have : toVal a ≠ toVal b := fun e => h (toVal_inj e)
    simp [h, this]

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

omit [LogosFacts] in
theorem eval_apply_cons_toVal (M : SmtModel) (hv a : MVal)
    (h : (∃ s dd i, hv = .dtc s dd i) ∨ ∃ f x, hv = .app f x) :
    __smtx_model_eval_apply M (toVal hv) (toVal a) = SmtValue.Apply (toVal hv) (toVal a) := by
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases a <;> rfl

omit [LogosFacts] in
/-- **A constructor applied to arguments has its value.** -/
theorem eval_chain (M : Model) : ∀ (vs : List MVal) (ts : List SmtTerm) (h : SmtTerm) (hv : MVal),
    List.Forall₂ (fun t v => __smtx_model_eval (toSmtModel M) t = toVal v) ts vs →
    ((∃ s dd i, h = SmtTerm.DtCons s dd i) ∨ ∃ a b, h = SmtTerm.Apply a b) →
    ((∃ s dd i, hv = .dtc s dd i) ∨ ∃ f x, hv = .app f x) →
    __smtx_model_eval (toSmtModel M) h = toVal hv →
    __smtx_model_eval (toSmtModel M) (ts.foldl SmtTerm.Apply h) = toVal (vs.foldl .app hv)
  | [], [], _, _, .nil, _, _, hh => hh
  | v :: vs, t :: ts, h, hv, .cons ht hr, hs, hvs, hh => by
    simp only [List.foldl]
    refine eval_chain M vs ts _ _ hr (Or.inr ⟨_, _, rfl⟩) (Or.inr ⟨_, _, rfl⟩) ?_
    have e : __smtx_model_eval (toSmtModel M) (SmtTerm.Apply h t) =
        __smtx_model_eval_apply (toSmtModel M) (__smtx_model_eval (toSmtModel M) h)
          (__smtx_model_eval (toSmtModel M) t) := by
      rcases hs with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rw [__smtx_model_eval.eq_def]
    rw [e, hh, ht, eval_apply_cons_toVal _ _ _ hvs]
    rfl

omit [LogosFacts] in
theorem lookup_sound {M : Model} {x : native_String} {T : SmtType} {v : MVal} (h : M.lookup x T = some v) :
    native_model_lookup (toSmtModel M) x T = toVal v := by
  simp only [native_model_lookup, model_key, toSmtModel, Bool.false_eq_true, ↓reduceIte, h]

omit [LogosFacts] in
theorem wrongSelName_eq (i j : Nat) : Model.wrongSelName i j = native_wrong_apply_sel_id i j := rfl

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
  · rename_i i
    exact ⟨hS, fun v h => by
      cases h; simpa [Node.toSmt, Node.toEo, Const.toEo, toVal] using eval_numeral_term (toSmtModel M) i⟩
  · rename_i q
    exact ⟨hS, fun v h => by
      cases h; simpa [Node.toSmt, Node.toEo, Const.toEo, toVal, native_rat_to_real] using
        eval_rational_term (toSmtModel M) q⟩
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
  · -- a constructor applied
    rename_i _ T idx cs
    split
    · exact ⟨hS, fun v h => by cases h⟩
    · rename_i sc ddc ic hc
      obtain ⟨a, d, he⟩ := dtCons_toEo hc
      have hsmt : (Node.const (.dtCons T idx)).toSmt = SmtTerm.DtCons sc ddc ic := by
        simp only [Model.consOf?] at hc; split at hc <;> simp_all
      obtain ⟨hS1, hv1⟩ := evList_sound M n IH cs.toList S hS
      rcases e1 : M.evList n cs.toList S with ⟨r1, S1⟩
      rw [e1] at hS1 hv1
      try dsimp only
      cases r1 with
      | none => exact ⟨hS1, fun v h => by cases h⟩
      | some vs =>
        refine ⟨hS1, fun v h => ?_⟩
        cases h
        rw [toSmt_cons _ cs (he ▸ DHead.dtcons a d idx), hsmt]
        refine eval_chain M vs _ _ _ ((List.forall₂_map_left_iff).2 (hv1 vs rfl))
          (Or.inl ⟨_, _, _, rfl⟩) (Or.inl ⟨_, _, _, rfl⟩) ?_
        rw [__smtx_model_eval.eq_def]; rfl
  · -- a tester applied
    rename_i _ T idx cs
    split
    · rename_i sc ddc ic x hc hcs
      have hsmt : (Node.const (.dtCons T idx)).toSmt = SmtTerm.DtCons sc ddc ic := by
        simp only [Model.consOf?] at hc; split at hc <;> simp_all
      obtain ⟨hS1, hv1⟩ := IH x S hS
      rcases e1 : M.ev n x S with ⟨r1, S1⟩
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
        rw [show SmtValue.DtCons sc ddc ic = toVal (.dtc sc ddc ic) from rfl, veq_toVal]
        rfl
    · exact ⟨hS, fun v h => by cases h⟩
  · -- a selector applied
    rename_i _ T idx jdx cs
    split
    · rename_i sc ddc ic jc x hc hcs
      obtain ⟨a, d, he⟩ := dtSel_toEo hc
      have hsmt : (Node.const (.dtSel T idx jdx)).toSmt = SmtTerm.DtSel sc ddc ic jc := by
        simp only [Model.selOf?] at hc; split at hc <;> simp_all
      obtain ⟨hS1, hv1⟩ := IH x S hS
      rcases e1 : M.ev n x S with ⟨r1, S1⟩
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
        rw [show SmtValue.DtCons sc ddc ic = toVal (.dtc sc ddc ic) from rfl, veq_toVal]
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
theorem solveScript_sat (sc : Script) (u : UserOptions) (ee pp wp co vs : Bool)
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co vs = .ok (out, r))
    (hs : r.answer = .sat) {opts : PPOptions} {as : List Node}
    (hin : ppInput sc u = .ok (opts, as)) :
    ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
  simp only [solveScript, hin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · -- whichever solved it, the answer is `sat` only if the model satisfies the
    -- input
    have key : ∀ (o : NodeOrder) (r0 : Solver.Result), (if r0.answer != .sat then r0 else
        if (Solver.buildModel r0.ee (Solver.relevantTerms r0.asserted) (Solver.freeConsts as)
            (engineDefs as opts pp o) as r0.arithModel).satisfies as then
          { r0 with model := some (Solver.buildModel r0.ee (Solver.relevantTerms r0.asserted)
            (Solver.freeConsts as) (engineDefs as opts pp o) as r0.arithModel) }
        else { r0 with answer := .unknown, uncertified := some "the model does not satisfy the input" }).answer = .sat →
        ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
      intro _ r0 hs
      split at hs
      · rename_i hne
        simp [hs] at hne
      · split at hs
        · rename_i hsat
          exact ⟨_, Solver.satisfies_sound hsat⟩
        · simp at hs
    split at h
    · try simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact key _ _ hs
    · split at h
      · simp at h
      · try simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact key _ _ hs

end Telos.Frontend
