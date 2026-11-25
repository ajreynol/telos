import TelosProofs.Core.AciNorm

/-!
# `aci_norm` steps on concatenations of strings are CPC steps

`aciConcat_provesEq`: under `AciConcat.Ok`, Logos's checker accepts
`[aci_norm (= n m)]`. Logos's normal form of a concatenation is read as the list
of its components (`A`), in order; `chain l` is the Eunoia list of `l`.
-/

open Eo Smtm SmtEval

-- (the proofs are about Logos's own list constructors)
set_option linter.internalConstructors false

namespace Telos

namespace AciConcatProof

open AciProof (eo_eq eo_ite_true eo_ite_false requires_true mk_apply)
open Node (termTy termTy_str_concat termTy_toEo)

abbrev f : Term := .UOp .str_concat
abbrev nil : Term := .String []

/-- The Eunoia list `(str.++ x₁ (str.++ x₂ … ""))`. -/
def chain (l : List Term) : Term := eoRightAssocNil .str_concat nil l

/-- The components of `t`, as `__get_a_norm_rec`. -/
def A : Term → List Term
  | .Apply (.Apply g x) y =>
    if g = f then A x ++ A y
    else [.Apply (.Apply g x) y]
  | t => if t = nil then [] else [t]

theorem chain_cons (x : Term) (l : List Term) : chain (x :: l) = .Apply (.Apply f x) (chain l) := rfl

theorem chain_ne (l : List Term) : chain l ≠ .Stuck := by
  cases l <;> simp [chain, eoRightAssocNil, eoApp2]

theorem get_nil (l : List Term) : __eo_get_nil_rec f (chain l) = nil := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show __eo_requires f f (__eo_get_nil_rec f (chain l)) = _
    rw [ih]; simp [__eo_requires, native_ite, native_teq, native_not]

theorem is_list (l : List Term) : __eo_is_list f (chain l) = .Boolean true := by
  have : __eo_is_list f (chain l) = __eo_is_ok (__eo_get_nil_rec f (chain l)) := by
    have hc := chain_ne l
    unfold __eo_is_list
    split <;> simp_all
  rw [this, get_nil]
  rfl

theorem concat_rec (l r : List Term) : __eo_list_concat_rec (chain l) (chain r) = chain (l ++ r) := by
  induction l with
  | nil =>
    have hr := chain_ne r
    show __eo_list_concat_rec nil (chain r) = chain r
    unfold __eo_list_concat_rec
    split <;> simp_all
  | cons x l ih =>
    have hr := chain_ne r
    rw [chain_cons, List.cons_append, chain_cons, ← ih]
    have : __eo_list_concat_rec (.Apply (.Apply f x) (chain l)) (chain r) =
        __eo_mk_apply (.Apply f x) (__eo_list_concat_rec (chain l) (chain r)) := by
      rw [__eo_list_concat_rec]; exact hr
    rw [this, ih, mk_apply (by simp) (chain_ne _)]

/-- A component. -/
theorem leaf {t : Term} (ht : t ≠ .Stuck) (he : t ≠ nil) : __eo_l_1___get_a_norm_rec f nil t = chain [t] := by
  have : __eo_l_1___get_a_norm_rec f nil t =
      __eo_ite (__eo_eq nil t) nil (__eo_l_2___get_a_norm_rec f nil t) := by
    rw [__eo_l_1___get_a_norm_rec] <;> simp_all
  rw [this, eo_eq (by simp) ht, decide_eq_false he, eo_ite_false]
  rw [__eo_l_2___get_a_norm_rec] <;> simp_all [chain, eoRightAssocNil, eoApp2]

/-- **Logos's normal form is the list of the components.** -/
theorem rec_eq : ∀ {t : Term}, AciProof.Good .str_concat t → __get_a_norm_rec f nil t = chain (A t) := by
  intro t
  fun_induction A t with
  | case1 x y ihx ihy =>
    intro hg
    obtain ⟨hx, hy⟩ := hg.2 rfl
    have : __get_a_norm_rec f nil (.Apply (.Apply f x) y) =
        __eo_ite (__eo_eq f f) (__eo_list_concat f (__get_a_norm_rec f nil x) (__get_a_norm_rec f nil y))
          (__eo_l_1___get_a_norm_rec f nil (.Apply (.Apply f x) y)) := by
      rw [__get_a_norm_rec] <;> simp
    rw [this, eo_eq (by simp) (by simp), decide_eq_true rfl, eo_ite_true, ihx hx, ihy hy, __eo_list_concat, is_list,
      is_list, requires_true, requires_true, concat_rec]
  | case2 g x y hne =>
    intro hg
    have : __get_a_norm_rec f nil (.Apply (.Apply g x) y) =
        __eo_ite (__eo_eq f g) (__eo_list_concat f (__get_a_norm_rec f nil x) (__get_a_norm_rec f nil y))
          (__eo_l_1___get_a_norm_rec f nil (.Apply (.Apply g x) y)) := by
      rw [__get_a_norm_rec] <;> simp
    rw [this, eo_eq (by simp) hg.1, decide_eq_false hne, eo_ite_false]
    exact leaf (by simp) (by simp)
  | case3 =>
    intro _
    have h1 : __get_a_norm_rec f nil nil = __eo_l_1___get_a_norm_rec f nil nil := by
      rw [__get_a_norm_rec] <;> simp
    have h2 : __eo_l_1___get_a_norm_rec f nil nil =
        __eo_ite (__eo_eq nil nil) nil (__eo_l_2___get_a_norm_rec f nil nil) := by
      rw [__eo_l_1___get_a_norm_rec] <;> simp
    rw [h1, h2, eo_eq (by simp) (by simp), decide_eq_true rfl, eo_ite_true]
    rfl
  | case4 t hn he =>
    intro hg
    have hs : t ≠ .Stuck := by
      unfold AciProof.Good at hg
      split at hg
      · simp
      · exact hg
    have : __get_a_norm_rec f nil t = __eo_l_1___get_a_norm_rec f nil t := by
      unfold __get_a_norm_rec
      split <;> simp_all
    rw [this]
    exact leaf hs he

/-- The normal form of a list of components: `""`, the component, or the list. -/
def form : List Term → Term
  | [x] => x
  | l => chain l

theorem get_a {x y : Term} (hg : AciProof.Good .str_concat (.Apply (.Apply f x) y))
    (ht : __eo_typeof (.Apply (.Apply f x) y) = .Apply (.UOp .Seq) (.UOp .Char)) :
    __get_aci_normal_form (.Apply (.Apply f x) y) = form (A (.Apply (.Apply f x) y)) := by
  show __get_a_norm (.Apply (.Apply f x) y) = _
  rw [__get_a_norm, ht, show __eo_nil f (.Apply (.UOp .Seq) (.UOp .Char)) = nil from rfl, rec_eq hg,
    __eo_list_singleton_elim, is_list, requires_true]
  generalize A _ = l
  match l with
  | [] => rfl
  | [x] =>
    show __eo_ite (__eo_is_list_nil f nil) x _ = _
    rw [show __eo_is_list_nil f nil = .Boolean true from rfl, eo_ite_true]; rfl
  | x :: y :: l =>
    show __eo_ite (__eo_is_list_nil f (.Apply (.Apply f y) (chain l))) x _ = _
    rw [show __eo_is_list_nil f (.Apply (.Apply f y) (chain l)) = .Boolean false from rfl, eo_ite_false]; rfl

/-! ## Typing -/

/-- The SMT types of strings. -/
def Str (t : Term) : Prop := termTy t = .Seq .Char

theorem str_inv {x y : Term} (h : Str (.Apply (.Apply f x) y)) : Str x ∧ Str y := by
  unfold Str at *
  rw [termTy_str_concat] at h
  unfold __smtx_typeof_seq_op_2 at h
  split at h
  · rename_i T U hx hy
    by_cases e : T = U
    · subst e
      simp [native_ite, native_Teq] at h
      subst h
      exact ⟨hx, hy⟩
    · simp [native_ite, native_Teq, e] at h
  · cases h

theorem good_of_str : ∀ t : Term, Str t → AciProof.Good .str_concat t := by
  intro t
  fun_induction AciProof.Good .str_concat t with
  | case1 g x y ihx ihy =>
    intro h
    refine ⟨?_, ?_⟩
    · rintro rfl
      unfold Str at h
      rw [AciProof.ty_stuck_app] at h; cases h
    · rintro rfl
      obtain ⟨hx, hy⟩ := str_inv h
      exact ⟨ihx hx, ihy hy⟩
  | case2 t ht =>
    intro h e
    subst e
    unfold Str at h
    rw [AciProof.ty_stuck] at h; cases h

theorem str_mem : ∀ t : Term, Str t → ∀ x ∈ A t, Str x := by
  intro t
  fun_induction A t with
  | case1 x y ihx ihy =>
    intro h z hz
    obtain ⟨hx, hy⟩ := str_inv h
    rcases List.mem_append.mp hz with hz | hz
    · exact ihx hx z hz
    · exact ihy hy z hz
  | case2 g x y hne => intro h z hz; rw [List.mem_singleton] at hz; subst hz; exact h
  | case3 => intro _ z hz; cases hz
  | case4 t hn he => intro h z hz; rw [List.mem_singleton] at hz; subst hz; exact h

/-- A term of a string type has the Eunoia type of strings: by the type of its
equation with `""`. -/
theorem eo_typeof_str [LogosFacts] {t : Term} (h : Str t) : __eo_typeof t = .Apply (.UOp .Seq) (.UOp .Char) := by
  have hb : __smtx_typeof (__eo_to_smt (eoApp2 UserOp.eq t nil)) = SmtType.Bool := by
    show termTy (.Apply (.Apply (.UOp .eq) t) nil) = _
    rw [Node.termTy_eq, h, Node.termTy_string]; rfl
  have h := LogosFacts.eo_typeof_bool _ hb
  replace h : __eo_typeof_eq (__eo_typeof t) (.Apply (.UOp .Seq) (.UOp .Char)) = .Bool := h
  unfold __eo_typeof_eq at h
  split at h
  · cases h
  · cases h
  · rename_i T _ hT
    by_cases e : Term.Apply (.UOp .Seq) (.UOp .Char) = __eo_typeof t
    · exact e.symm
    · rw [eo_eq (by assumption) (by simp), decide_eq_false e] at h
      simp [__eo_requires, native_ite, native_teq] at h

/-! ## The rule -/

theorem form_str {l : List Term} (h : ∀ x ∈ l, Str x) : Str (form l) := by
  have hc : ∀ l : List Term, (∀ x ∈ l, Str x) → Str (chain l) := by
    intro l
    induction l with
    | nil =>
      intro _
      show termTy (Term.String []) = _
      rw [Node.termTy_string]; rfl
    | cons x l ih =>
      intro h
      show termTy (.Apply (.Apply f x) (chain l)) = _
      rw [termTy_str_concat, h x (by simp), ih fun y hy => h y (by simp [hy])]
      rfl
  unfold form
  split
  · exact h _ (by simp)
  · exact hc l h

theorem str_ne {t : Term} (h : Str t) : t ≠ .Stuck := by
  rintro rfl
  unfold Str at h
  rw [AciProof.ty_stuck] at h; cases h

theorem ty_sorted (g x : Term) : ¬ Str (.Apply (.Apply (.UOp ._at__at_aci_sorted) g) x) := by
  unfold Str termTy
  rw [show __eo_to_smt (.Apply (.Apply (.UOp ._at__at_aci_sorted) g) x) =
    SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt g)) (__eo_to_smt x) from rfl]
  rw [__smtx_typeof.eq_def]
  dsimp only
  rw [__smtx_typeof.eq_def (SmtTerm.Apply SmtTerm.None _)]
  dsimp only
  rw [__smtx_typeof.eq_def SmtTerm.None]
  simp [__smtx_typeof_apply]

/-- Comparing two strings. -/
theorem norm_eq {s t : Term} (hs : Str s) (ht : Str t) : __aci_norm_eq s t = .Boolean (decide (t = s)) := by
  have hsS := str_ne hs
  have htS := str_ne ht
  have hno : ∀ g x, s ≠ .Apply (.Apply (.UOp ._at__at_aci_sorted) g) x := fun g x e => ty_sorted g x (e ▸ hs)
  have h1 : __aci_norm_eq s t = __eo_ite (__eo_eq s t) (.Boolean true) (__eo_l_1___aci_norm_eq s t) := by
    rw [__aci_norm_eq] <;> simp_all
  have h2 : __eo_l_1___aci_norm_eq s t = __eo_l_2___aci_norm_eq s t := by
    unfold __eo_l_1___aci_norm_eq
    split <;> simp_all
  have h3 : __eo_l_2___aci_norm_eq s t = __eo_l_3___aci_norm_eq s t := by
    unfold __eo_l_2___aci_norm_eq
    split <;> simp_all
  have h4 : __eo_l_3___aci_norm_eq s t = .Boolean false := by
    rw [__eo_l_3___aci_norm_eq] <;> simp_all
  rw [h1, eo_eq hsS htS, h2, h3, h4]
  by_cases e : t = s
  · rw [decide_eq_true e, eo_ite_true]
  · rw [decide_eq_false e, eo_ite_false]

/-- **`aci_norm` accepts two concatenations with the same components.** -/
theorem prog [LogosFacts] {x y b : Term} (ha : Str (.Apply (.Apply f x) y)) (hb : Str b)
    (hs : A (.Apply (.Apply f x) y) = A b) :
    __eo_prog_aci_norm (eoApp2 UserOp.eq (.Apply (.Apply f x) y) b) = eoApp2 UserOp.eq (.Apply (.Apply f x) y) b := by
  have hfa := get_a (good_of_str _ ha) (eo_typeof_str ha)
  have hsa := form_str (str_mem _ ha)
  show __eo_requires (__eo_ite (__aci_norm_eq (__get_aci_normal_form (.Apply (.Apply f x) y)) b) (.Boolean true)
    (__eo_ite (__aci_norm_eq (__get_aci_normal_form b) (.Apply (.Apply f x) y)) (.Boolean true)
      (__aci_norm_eq (__get_aci_normal_form (.Apply (.Apply f x) y)) (__get_aci_normal_form b)))) (.Boolean true) _ = _
  rw [hfa, norm_eq hsa hb]
  by_cases hc : ∃ x' y', b = .Apply (.Apply f x') y'
  · obtain ⟨x', y', rfl⟩ := hc
    have hfb := get_a (good_of_str _ hb) (eo_typeof_str hb)
    have hsb := form_str (str_mem _ hb)
    rw [hfb, norm_eq hsb ha, norm_eq hsa hsb, hs]
    rw [decide_eq_true (rfl : form (A (.Apply (.Apply f x') y')) = _)]
    cases decide ((Term.Apply (.Apply f x') y') = form (A (.Apply (.Apply f x') y'))) <;>
      cases decide ((Term.Apply (.Apply f x) y) = form (A (.Apply (.Apply f x') y'))) <;>
      simp only [eo_ite_true, eo_ite_false, requires_true] <;> rfl
  · have hA : A b = if b = nil then [] else [b] := by
      unfold A
      split
      · rename_i g x' y'
        rw [ite_eq_right fun e => hc ⟨x', y', by rw [e]⟩, ite_eq_right (by simp)]
      · rfl
    have hf : form (A (.Apply (.Apply f x) y)) = b := by
      rw [hs, hA]
      split
      · rename_i e; rw [e]; rfl
      · rfl
    rw [hf, decide_eq_true rfl, eo_ite_true, requires_true]
    rfl

/-! ## The components of a node -/

theorem A_chain (l : List Term) : A (chain l) = l.flatMap A := by
  induction l with
  | nil => simp [chain, eoRightAssocNil, A]
  | cons x l ih => rw [chain_cons, A, ite_eq_left rfl, ih]; rfl

theorem toEo_concat {cs : Array Node} (h : AciConcat.isConcat cs = true) :
    (Node.app (.kind .STRING_CONCAT) cs).toEo = chain (cs.toList.map Node.toEo) := by
  unfold AciConcat.isConcat at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hc⟩ := h
  obtain ⟨l⟩ := cs
  match l, hs, hc with
  | a :: b :: l, _, hc =>
    have ha : a.smtType = .Seq .Char := by
      simp at hc
      rwa [Node.smtTypeF_eq] at hc
    rw [Node.toEo_app]
    show eoRightAssocNil .str_concat (typedNil .str_concat a.toEo) _ = _
    rw [Node.typedNil_eq, termTy_toEo, ha]
    rfl

/-- **The components of a node are those of its leaves.** -/
theorem A_leaves : ∀ n : Node, A n.toEo = (AciConcat.leaves n).flatMap fun l => A l.toEo
  | .const (.string w) => by
    rw [AciConcat.leaves]
    split
    · rename_i e
      subst e
      simp [Node.toEo, Const.toEo, A]
    · simp
  | .app (.kind k) cs => by
    rw [AciConcat.leaves]
    split
    · rename_i e
      obtain ⟨rfl, hs⟩ := e
      have ih : ∀ c ∈ cs.toList, A c.toEo = (AciConcat.leaves c).flatMap fun l => A l.toEo :=
        fun c hc => A_leaves c
      rw [toEo_concat hs, A_chain]
      simp only [Array.toList_attach, List.flatMap_map, List.flatMap_assoc]
      have : ∀ (l : List Node) (hl : ∀ c ∈ l, c ∈ cs), (∀ c ∈ l, c ∈ cs.toList) →
          l.flatMap (fun c => A c.toEo) =
            (l.attachWith (· ∈ cs) hl).flatMap fun c => (AciConcat.leaves c.1).flatMap fun l => A l.toEo := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons c l ihl =>
          intro hl hm
          simp only [List.flatMap_cons, List.attachWith_cons]
          rw [ih c (hm c (by simp)), ihl (fun d hd => hl d (by simp [hd])) (fun d hd => hm d (by simp [hd]))]
      exact this cs.toList _ fun c hc => hc
    · simp
  | .const (.integer _) | .const (.rational _) | .const (.boolean _) | .const (.bitVector ..) | .const (.emptySet _)
  | .const (.emptySeq _) | .const (.dtCons ..) | .const (.dtSel ..) | .var .. | .boundVar .. | .skolem ..
  | .app (.indexed ..) _ | .app (.node ..) _ => by
    rw [AciConcat.leaves] <;> simp
termination_by n => sizeOf n
decreasing_by all_goals (have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹_›); simp_all; omega)

end AciConcatProof

open AciConcatProof Node

/-- **An `aci_norm` step on concatenations of strings with the same components
is a CPC step.** -/
theorem aciConcat_provesEq [LogosFacts] {n m : Node} (h : AciConcat.Ok n m) : ProvesEq (StaticProc.aciCmds n m) n m := by
  obtain ⟨hn, hl, hnT, hmT⟩ := h
  rw [smtTypeF_eq] at hnT hmT
  split at hn
  · rename_i cs
    obtain ⟨x, y, he⟩ : ∃ x y, (Node.app (.kind .STRING_CONCAT) cs).toEo = .Apply (.Apply f x) y := by
      rw [toEo_concat hn]
      unfold AciConcat.isConcat at hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
      obtain ⟨l⟩ := cs
      match l, hn.1 with
      | c :: l, _ => exact ⟨c.toEo, _, rfl⟩
    have ha : Str (.Apply (.Apply f x) y) := by
      show termTy _ = _
      rw [← he, termTy_toEo, hnT]
    have hb : Str m.toEo := by
      show termTy _ = _
      rw [termTy_toEo, hmT]
    have hstep := prog ha hb (by rw [← he, A_leaves, A_leaves m, hl])
    have hf : eqFormula (Node.app (.kind .STRING_CONCAT) cs) m = eoApp2 UserOp.eq (.Apply (.Apply f x) y) m.toEo := by
      rw [eqFormula, he]
    have hty : __smtx_typeof (__eo_to_smt (eqFormula (Node.app (.kind .STRING_CONCAT) cs) m)) = SmtType.Bool := by
      rw [typeof_eqFormula, hnT, hmT]; rfl
    refine Template.provesEq_one ⟨by rw [eoHasSmtTranslation, hty]; simp, trivial⟩ ?_ hty
    show __eo_prog_aci_norm (eqFormula (Node.app (.kind .STRING_CONCAT) cs) m) = _
    rw [hf]; exact hstep
  · exact hn.elim

end Telos
