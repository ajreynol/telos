import TelosProofs.Core.AciConcat
import TelosProofs.Core.Semantic

/-!
# Length-based splits of string equalities are equivalences

`SemProc.strSplit_equiv`: under `StrSplit.ok`, an equality of two
concatenations of strings is equivalent to the conjunction of the equalities of
its prefixes and of its suffixes (`Telos/Core/StrSplit.lean`).

In a well-formed model, each component of a well-typed concatenation of
strings evaluates to a sequence (`str.++` of anything else is `NotValue`, which
has no type), packed with the element type `Char`, and the concatenation to the
sequence of their lists, appended (`chain_sem`). The prefixes' lists have the
same length (`len_flatMap`: the length of a list of components is the sum of
those of the non-constant components and of the constants'), so the lists of
the two sides are equal iff the prefixes' and the suffixes' are
(`List.append_inj`).
-/

open Eo Smtm SmtEval

namespace Telos

namespace StrSplitProof

open AciConcatProof (chain chain_cons)

/-- The elements of a sequence value; `[]` for any other value. -/
def L : SmtValue → List SmtValue
  | .Seq s => native_unpack_seq s
  | _ => []

theorem unpack_pack (T : SmtType) : ∀ l : List SmtValue, native_unpack_seq (native_pack_seq T l) = l
  | [] => rfl
  | v :: l => by simp [native_pack_seq, native_unpack_seq, unpack_pack T l]

theorem elem_pack (T : SmtType) : ∀ l : List SmtValue,
    __smtx_elem_typeof_seq_value (native_pack_seq T l) = T
  | [] => rfl
  | v :: l => by simp [native_pack_seq, __smtx_elem_typeof_seq_value, elem_pack T l]

/-- A sequence value of type `Seq T` is its elements packed with `T`. -/
theorem pack_unpack : ∀ (s : SmtSeq) (T : SmtType), __smtx_typeof_seq_value s = SmtType.Seq T →
    native_pack_seq T (native_unpack_seq s) = s
  | .empty U, T, h => by
    simp only [__smtx_typeof_seq_value, SmtType.Seq.injEq] at h
    subst h; rfl
  | .cons v vs, T, h => by
    simp only [__smtx_typeof_seq_value, native_ite, native_Teq] at h
    by_cases hc : SmtType.Seq (__smtx_typeof_value v) = __smtx_typeof_seq_value vs
    · simp only [hc, decide_true, ite_true] at h
      have e := pack_unpack vs T h
      simp only [native_unpack_seq, native_pack_seq, e]
    · simp [hc] at h

theorem pack_inj {T : SmtType} {l₁ l₂ : List SmtValue}
    (h : native_pack_seq T l₁ = native_pack_seq T l₂) : l₁ = l₂ := by
  have := congrArg native_unpack_seq h
  rwa [unpack_pack, unpack_pack] at this

theorem toSmt_cons (x : Term) (l : List Term) :
    __eo_to_smt (chain (x :: l)) = SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt (chain l)) := rfl

theorem toSmt_nil : __eo_to_smt (chain []) = SmtTerm.String [] := rfl

theorem typeof_str_concat (a b : SmtTerm) : __smtx_typeof (SmtTerm.str_concat a b) =
    __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

theorem eval_str_concat (M : SmtModel) (a b : SmtTerm) : __smtx_model_eval M (SmtTerm.str_concat a b) =
    __smtx_model_eval_str_concat (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

theorem typeof_empty : __smtx_typeof (SmtTerm.String []) = SmtType.Seq SmtType.Char := by
  rw [__smtx_typeof.eq_def]; rfl

theorem eval_empty (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.String []) = SmtValue.Seq (native_pack_seq SmtType.Char []) := by
  rw [__smtx_model_eval.eq_def]; rfl

theorem seq_op_2_char {T U : SmtType} (h : __smtx_typeof_seq_op_2 T U = SmtType.Seq SmtType.Char) :
    T = SmtType.Seq SmtType.Char ∧ U = SmtType.Seq SmtType.Char := by
  cases T <;> cases U <;> simp_all [__smtx_typeof_seq_op_2, native_ite, native_Teq]
  split at h <;> simp_all

/-- A chain of strings is a string. -/
theorem chain_typed : ∀ l : List Term, (∀ x ∈ l, __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) →
    __smtx_typeof (__eo_to_smt (chain l)) = SmtType.Seq SmtType.Char
  | [], _ => by rw [toSmt_nil]; exact typeof_empty
  | x :: l, h => by
    rw [toSmt_cons, typeof_str_concat, h x (by simp), chain_typed l fun y hy => h y (by simp [hy])]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

variable [LogosFacts]

/-- **The value of a chain of strings**: each component is a string, its value
the packing of its elements, and the chain's value the packing of theirs,
appended. -/
theorem chain_sem (M : SmtModel) (hM : model_wf M) : ∀ l : List Term,
    __smtx_typeof (__eo_to_smt (chain l)) = SmtType.Seq SmtType.Char →
    (∀ x ∈ l, __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char ∧
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Seq (native_pack_seq SmtType.Char (L (__smtx_model_eval M (__eo_to_smt x))))) ∧
    __smtx_model_eval M (__eo_to_smt (chain l)) =
      SmtValue.Seq (native_pack_seq SmtType.Char (l.flatMap fun x => L (__smtx_model_eval M (__eo_to_smt x))))
  | [], _ => by
    refine ⟨by simp, ?_⟩
    rw [toSmt_nil, eval_empty]; rfl
  | x :: l, h => by
    rw [toSmt_cons, typeof_str_concat] at h
    obtain ⟨hx, hl⟩ := seq_op_2_char h
    obtain ⟨ih₁, ih₂⟩ := chain_sem M hM l hl
    -- the concatenation has a type, so its value is not `NotValue`: `x`'s is a sequence
    have hv := LogosFacts.eval_typed M (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt (chain l))) hM
      (by rw [typeof_str_concat, hx, hl]; simp [__smtx_typeof_seq_op_2, native_ite, native_Teq])
    rw [typeof_str_concat, hx, hl, eval_str_concat, ih₂] at hv
    have hxv := LogosFacts.eval_typed M (__eo_to_smt x) hM (by rw [hx]; simp)
    rw [hx] at hxv
    obtain ⟨sx, hex⟩ : ∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx := by
      cases hex : __smtx_model_eval M (__eo_to_smt x) <;> rw [hex] at hv <;>
        simp only [__smtx_model_eval_str_concat, __smtx_typeof_value] at hv <;>
        first | exact ⟨_, rfl⟩ | cases hv
    rw [hex] at hxv
    have hsx := pack_unpack sx SmtType.Char hxv
    have hxe : __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Seq (native_pack_seq SmtType.Char (L (__smtx_model_eval M (__eo_to_smt x)))) := by
      rw [hex]; simp only [L]; rw [hsx]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨hx, hxe⟩
      · exact ih₁ y hy
    · have he : __smtx_elem_typeof_seq_value sx = SmtType.Char := by rw [← hsx, elem_pack]
      rw [toSmt_cons, eval_str_concat, hex, ih₂, List.flatMap_cons, hex]
      simp only [L, __smtx_model_eval_str_concat, native_seq_concat]
      rw [unpack_pack, he]

omit [LogosFacts] in
theorem toSmt_eq2 (a b : Node) :
    (Node.app (.kind .EQUAL) #[a, b]).toSmt = SmtTerm.eq a.toSmt b.toSmt := by
  unfold Node.toSmt
  rw [Node.toEo_app]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]
  rfl

omit [LogosFacts] in
theorem toSmt_and2 (a b : Node) :
    (Node.app (.kind .AND) #[a, b]).toSmt =
      SmtTerm.and a.toSmt (SmtTerm.and b.toSmt (SmtTerm.Boolean true)) := by
  unfold Node.toSmt
  rw [toEo_and _ (by simp)]
  rfl

omit [LogosFacts] in
theorem toSmt_string (w : List Nat) : (Node.const (.string w)).toSmt = SmtTerm.String w := by
  simp [Node.toSmt, Node.toEo, Const.toEo]; rfl

omit [LogosFacts] in
theorem eval_string (M : SmtModel) (w : List Nat) :
    __smtx_model_eval M (SmtTerm.String w) = SmtValue.Seq (native_pack_seq SmtType.Char (w.map SmtValue.Char)) := by
  rw [__smtx_model_eval.eq_def]; rfl

omit [LogosFacts] in
theorem seq_op_2_char_left {U : SmtType}
    (h : __smtx_typeof_seq_op_2 (SmtType.Seq SmtType.Char) U ≠ SmtType.None) :
    U = SmtType.Seq SmtType.Char := by
  cases U <;> simp_all [__smtx_typeof_seq_op_2, native_ite, native_Teq]

omit [LogosFacts] in
/-- A well-typed chain of strings whose first component is a string is a string. -/
theorem chain_char {x : Term} {l : List Term}
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char)
    (h : __smtx_typeof (__eo_to_smt (chain (x :: l))) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (chain (x :: l))) = SmtType.Seq SmtType.Char := by
  rw [toSmt_cons, typeof_str_concat, hx] at h ⊢
  rw [seq_op_2_char_left h]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

omit [LogosFacts] in
/-- The components of a chain of strings are strings. -/
theorem chain_types : ∀ l : List Term,
    __smtx_typeof (__eo_to_smt (chain l)) = SmtType.Seq SmtType.Char →
    ∀ x ∈ l, __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char
  | [], _ => by simp
  | x :: l, h => by
    rw [toSmt_cons, typeof_str_concat] at h
    obtain ⟨hx, hl⟩ := seq_op_2_char h
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact chain_types l hl y hy

/-- A component's value in a model is the packing of its elements. -/
def CompV (M : SmtModel) (c : Node) : Prop :=
  __smtx_model_eval M c.toSmt = SmtValue.Seq (native_pack_seq SmtType.Char (L (__smtx_model_eval M c.toSmt)))

/-- The elements of the values of components, appended. -/
noncomputable def els (M : SmtModel) (cs : List Node) : List SmtValue :=
  cs.flatMap fun c => L (__smtx_model_eval M c.toSmt)

omit [LogosFacts] in
theorem isConcat_of {c d : Node} {rest : List Node} (hc : __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char) :
    AciConcat.isConcat ⟨c :: d :: rest⟩ = true := by
  simp only [AciConcat.isConcat, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by simp, ?_⟩
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.any_some, decide_eq_true_eq]
  rw [Node.smtTypeF_eq]; exact hc

omit [LogosFacts] in
theorem toSmt_concat {cs : List Node} (hc : AciConcat.isConcat ⟨cs⟩ = true) :
    (Node.app (.kind .STRING_CONCAT) ⟨cs⟩).toSmt = __eo_to_smt (chain (cs.map Node.toEo)) := by
  unfold Node.toSmt; rw [AciConcatProof.toEo_concat hc]

omit [LogosFacts] in
/-- A concatenation of string components (`StrSplit.cat`) is a string. -/
theorem cat_type : ∀ (cs : List Node), cs ≠ [] → (∀ c ∈ cs, __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char) →
    __smtx_typeof (StrSplit.cat cs).toSmt = SmtType.Seq SmtType.Char
  | [], h, _ => absurd rfl h
  | [c], _, hc => hc c (by simp)
  | c :: d :: rest, _, hc => by
    show __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨c :: d :: rest⟩).toSmt = _
    rw [toSmt_concat (isConcat_of (hc c (by simp)))]
    apply chain_typed
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hc y hy

/-- **The value of a concatenation of components** (`StrSplit.cat`): the
packing of the components' elements. -/
theorem cat_eval (M : SmtModel) (hM : model_wf M) :
    ∀ (cs : List Node), cs ≠ [] → (∀ c ∈ cs, __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char) →
    (∀ c ∈ cs, CompV M c) →
    __smtx_model_eval M (StrSplit.cat cs).toSmt = SmtValue.Seq (native_pack_seq SmtType.Char (els M cs))
  | [], h, _, _ => absurd rfl h
  | [c], _, _, hv => by
    simp only [StrSplit.cat, els, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact hv c (by simp)
  | c :: d :: rest, hne, ht, _ => by
    have hty := cat_type (c :: d :: rest) hne ht
    show __smtx_model_eval M (Node.app (.kind .STRING_CONCAT) ⟨c :: d :: rest⟩).toSmt = _
    have hcc := isConcat_of (d := d) (rest := rest) (ht c (by simp))
    change __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨c :: d :: rest⟩).toSmt = _ at hty
    rw [toSmt_concat hcc] at hty ⊢
    rw [(chain_sem M hM _ hty).2, els, List.flatMap_map]
    rfl

omit [LogosFacts] in
/-- A well-typed concatenation of strings is a string, of string components. -/
theorem concat_types {as : List Node} (hc : AciConcat.isConcat ⟨as⟩ = true)
    (h : __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt ≠ SmtType.None) :
    __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt = SmtType.Seq SmtType.Char ∧
      ∀ c ∈ as, __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char := by
  rw [toSmt_concat hc] at h ⊢
  obtain ⟨hs, hf⟩ := by simpa only [AciConcat.isConcat, Bool.and_eq_true, decide_eq_true_eq] using hc
  match as, hs, hf with
  | a :: l, _, hf =>
    have ha : __smtx_typeof (__eo_to_smt a.toEo) = SmtType.Seq SmtType.Char := by
      simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.any_some, decide_eq_true_eq] at hf
      rw [Node.smtTypeF_eq] at hf; exact hf
    have hty := chain_char ha (by simpa using h)
    simp only [List.map_cons] at hty ⊢
    refine ⟨hty, fun c hc => ?_⟩
    exact chain_types _ hty c.toEo (by simpa using List.mem_map_of_mem (f := Node.toEo) hc)

/-- The value of a well-typed concatenation of strings, and its components'. -/
theorem concat_eval (M : SmtModel) (hM : model_wf M) {as : List Node} (hc : AciConcat.isConcat ⟨as⟩ = true)
    (h : __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt ≠ SmtType.None) :
    (∀ c ∈ as, CompV M c) ∧
      __smtx_model_eval M (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt =
        SmtValue.Seq (native_pack_seq SmtType.Char (els M as)) := by
  have hty := (concat_types hc h).1
  rw [toSmt_concat hc] at hty ⊢
  obtain ⟨h₁, h₂⟩ := chain_sem M hM _ hty
  refine ⟨fun c hc => (h₁ c.toEo (List.mem_map_of_mem hc)).2, ?_⟩
  rw [h₂, els, List.flatMap_map]; rfl

omit [LogosFacts] in
theorem wordLen_some {c : Node} {k : Nat} (h : StrSplit.wordLen c = some k) :
    ∃ w, c = .const (.string w) ∧ k = w.length := by
  unfold StrSplit.wordLen at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

omit [LogosFacts] in
/-- The length of the elements of components: those of the non-constant
components, and the constants' lengths. -/
theorem len_els (M : SmtModel) : ∀ cs : List Node,
    (els M cs).length = ((StrSplit.others cs).map fun c => (L (__smtx_model_eval M c.toSmt)).length).sum +
      StrSplit.wordsLen cs
  | [] => by simp [els, StrSplit.others, StrSplit.wordsLen]
  | c :: cs => by
    have ih := len_els M cs
    simp only [els, List.flatMap_cons, List.length_append] at ih ⊢
    cases hw : StrSplit.wordLen c with
    | none =>
      simp only [StrSplit.others, StrSplit.wordsLen, List.filter_cons, hw, Option.isNone_none,
        ite_true, List.map_cons, List.sum_cons, List.filterMap_cons] at ih ⊢
      omega
    | some k =>
      obtain ⟨w, rfl, rfl⟩ := wordLen_some hw
      have hL : (L (__smtx_model_eval M (Node.const (.string w)).toSmt)).length = w.length := by
        rw [toSmt_string, eval_string]; simp [L, unpack_pack]
      simp only [StrSplit.others, StrSplit.wordsLen, List.filter_cons, hw, Option.isNone_some,
        Bool.false_eq_true, ite_false, List.filterMap_cons, List.sum_cons, hL] at ih ⊢
      omega

omit [LogosFacts] in
/-- Components of equal lengths (`StrSplit.lenEq`) have elements of equal
lengths in every model. -/
theorem lenEq_els (M : SmtModel) {ps qs : List Node} (h : StrSplit.lenEq ps qs = true) :
    (els M ps).length = (els M qs).length := by
  simp only [StrSplit.lenEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [len_els, len_els, (h.1.map _).sum_eq, h.2]

omit [LogosFacts] in
theorem eval_eq_seq (a b : SmtSeq) :
    __smtx_model_eval_eq (SmtValue.Seq a) (SmtValue.Seq b) = SmtValue.Boolean (decide (a = b)) := by
  simp [__smtx_model_eval_eq, native_veq]

omit [LogosFacts] in
theorem sides_eq {n : Node} {as bs : List Node} (h : StrSplit.sides? n = some (as, bs)) :
    n = Node.app (.kind .EQUAL) #[Node.app (.kind .STRING_CONCAT) ⟨as⟩, Node.app (.kind .STRING_CONCAT) ⟨bs⟩] := by
  unfold StrSplit.sides? at h
  split at h
  · rename_i cs
    split at h
    · rename_i a b hcs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l⟩ := cs
      subst hcs
      rfl
    · cases h
  · cases h

/-- **Splits are equivalences.** -/
theorem strSplit_equiv (i j : Nat) (n m : Node) (h : StrSplit.ok i j n m = true) (hn : n.WellTyped) :
    n.Equiv m := by
  unfold StrSplit.ok at h
  split at h
  case h_2 => cases h
  rename_i as bs hsd
  have hn' := sides_eq hsd
  subst hn'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hca, hcb⟩, hi₀⟩, hi⟩, hj₀⟩, hj⟩, hlen⟩, hm⟩ := h
  have hm : m = StrSplit.target as bs i j := of_decide_eq_true hm
  subst hm
  have hnT : __smtx_typeof (SmtTerm.eq (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt
      (Node.app (.kind .STRING_CONCAT) ⟨bs⟩).toSmt) ≠ SmtType.None := by
    have := hn; unfold Node.WellTyped Node.smtType at this; rwa [toSmt_eq2] at this
  rw [typeof_eq_eq] at hnT
  have hAB : __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt ≠ SmtType.None ∧
      __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt =
        __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨bs⟩).toSmt := by
    unfold __smtx_typeof_eq __smtx_typeof_guard at hnT
    by_cases h₁ : __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt = SmtType.None <;>
      by_cases h₂ : __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨as⟩).toSmt =
        __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨bs⟩).toSmt <;>
      simp_all [native_ite, native_Teq]
  have hB : __smtx_typeof (Node.app (.kind .STRING_CONCAT) ⟨bs⟩).toSmt ≠ SmtType.None := hAB.2 ▸ hAB.1
  have hne : ∀ {l : List Node} {k : Nat}, 0 < k → k < l.length → l.take k ≠ [] ∧ l.drop k ≠ [] := by
    intro l k h₀ h₁
    refine ⟨?_, ?_⟩
    · intro e; rw [List.take_eq_nil_iff] at e; rcases e with e | e <;> simp_all
    · intro e; rw [List.drop_eq_nil_iff] at e; omega
  obtain ⟨tA, ctA⟩ := concat_types hca hAB.1
  obtain ⟨tB, ctB⟩ := concat_types hcb hB
  have subT : ∀ {l : List Node}, (∀ c ∈ l, __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char) → ∀ k,
      (∀ c ∈ l.take k, __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char) ∧
      (∀ c ∈ l.drop k, __smtx_typeof c.toSmt = SmtType.Seq SmtType.Char) :=
    fun hl k => ⟨fun c hc => hl c (List.mem_of_mem_take hc), fun c hc => hl c (List.mem_of_mem_drop hc)⟩
  have p₀t := cat_type (as.take i) (hne hi₀ hi).1 (subT ctA i).1
  have s₀t := cat_type (as.drop i) (hne hi₀ hi).2 (subT ctA i).2
  have p₁t := cat_type (bs.take j) (hne hj₀ hj).1 (subT ctB j).1
  have s₁t := cat_type (bs.drop j) (hne hj₀ hj).2 (subT ctB j).2
  refine (Node.equiv_iff _ _).2 ⟨hn, ⟨?_, fun M hM => ?_⟩⟩
  · unfold StrSplit.target
    rw [toSmt_eq2, toSmt_and2, toSmt_eq2, toSmt_eq2, typeof_eq_eq, tA, tB]
    have hb : __smtx_typeof (SmtTerm.and (SmtTerm.eq (StrSplit.cat (as.take i)).toSmt (StrSplit.cat (bs.take j)).toSmt)
        (SmtTerm.and (SmtTerm.eq (StrSplit.cat (as.drop i)).toSmt (StrSplit.cat (bs.drop j)).toSmt)
          (SmtTerm.Boolean true))) = SmtType.Bool := by
      rw [typeof_and_bool, typeof_and_bool, typeof_eq_eq, typeof_eq_eq, p₀t, s₀t, p₁t, s₁t,
        typeof_eq_eq_bool_iff]
      exact ⟨⟨by simp, rfl⟩, ⟨by simp, rfl⟩, typeof_true⟩
    rw [hb, typeof_eq_eq_bool_iff]
    exact ⟨by simp, rfl⟩
  · obtain ⟨cA, eA⟩ := concat_eval M hM hca hAB.1
    obtain ⟨cB, eB⟩ := concat_eval M hM hcb hB
    have subV : ∀ {l : List Node}, (∀ c ∈ l, CompV M c) → ∀ k, (∀ c ∈ l.take k, CompV M c) ∧ (∀ c ∈ l.drop k, CompV M c) :=
      fun hl k => ⟨fun c hc => hl c (List.mem_of_mem_take hc), fun c hc => hl c (List.mem_of_mem_drop hc)⟩
    have p₀e := cat_eval M hM (as.take i) (hne hi₀ hi).1 (subT ctA i).1 (subV cA i).1
    have s₀e := cat_eval M hM (as.drop i) (hne hi₀ hi).2 (subT ctA i).2 (subV cA i).2
    have p₁e := cat_eval M hM (bs.take j) (hne hj₀ hj).1 (subT ctB j).1 (subV cB j).1
    have s₁e := cat_eval M hM (bs.drop j) (hne hj₀ hj).2 (subT ctB j).2 (subV cB j).2
    unfold StrSplit.target
    rw [toSmt_eq2, toSmt_and2, toSmt_eq2, toSmt_eq2, model_eval_eq_eq, eA, eB, eval_and, eval_and,
      model_eval_eq_eq, model_eval_eq_eq, p₀e, s₀e, p₁e, s₁e, eval_true, eval_eq_seq, eval_eq_seq, eval_eq_seq]
    have hl := lenEq_els M hlen
    have hsplit : ∀ (l : List Node) (k : Nat), els M l = els M (l.take k) ++ els M (l.drop k) := by
      intro l k; unfold els; rw [← List.flatMap_append, List.take_append_drop]
    have key : decide (native_pack_seq SmtType.Char (els M as) = native_pack_seq SmtType.Char (els M bs)) =
        (decide (native_pack_seq SmtType.Char (els M (as.take i)) = native_pack_seq SmtType.Char (els M (bs.take j))) &&
          decide (native_pack_seq SmtType.Char (els M (as.drop i)) = native_pack_seq SmtType.Char (els M (bs.drop j)))) := by
      rw [hsplit as i, hsplit bs j]
      have inj : ∀ {l₁ l₂ : List SmtValue},
          (native_pack_seq SmtType.Char l₁ = native_pack_seq SmtType.Char l₂) ↔ l₁ = l₂ :=
        fun {l₁ l₂} => ⟨pack_inj, fun e => e ▸ rfl⟩
      rw [← Bool.decide_and]
      exact decide_eq_decide.2 (by
        rw [inj, inj, inj]
        exact ⟨fun e => List.append_inj e hl, fun ⟨e₁, e₂⟩ => by rw [e₁, e₂]⟩)
    rw [key]
    simp only [__smtx_model_eval_and, native_and, Bool.and_true]
    exact LogosFacts.value_rel_refl _

end StrSplitProof

end Telos
