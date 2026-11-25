import TelosProofs.Core.Template
import Telos.Core.Static

/-!
# `aci_norm` steps on conjunctions and disjunctions are CPC steps

`aci_provesEq`: under `Aci.Ok`, Logos's checker accepts
`[aci_norm (= n m)]`. Logos's normal form of an application of `f` (`and` or `or`)
is read as a list of terms (`N`), its operands without repetition; `chain l` is
the Eunoia list of `l`. The normal forms of two terms whose lists have the same
members are equal, or one a permutation of the other (`__eo_list_meq`).
-/

open Eo Smtm SmtEval

-- (the proofs are about Logos's own list constructors)
set_option linter.internalConstructors false

namespace Telos

namespace AciProof

/-- The Eunoia list `(f x₁ (f x₂ … nil))`. -/
def chain (op : UserOp) (u : Bool) (l : List Term) : Term :=
  eoRightAssocNil op (Term.Boolean u) l

/-- `l` without repetition, as `__eo_list_setof`. -/
def setofL : List Term → List Term
  | [] => []
  | x :: l => x :: (setofL l).filter fun y => decide (y ≠ x)

/-- `l` without the first `z`, as `__eo_list_erase`. -/
def eraseL : List Term → Term → List Term
  | [], _ => []
  | x :: l, z => if x = z then l else x :: eraseL l z

/-- The operands of `t`, as `__get_ai_norm_rec`. -/
def N (op : UserOp) (u : Bool) : Term → List Term
  | .Apply (.Apply g x) y =>
    if g = .UOp op then setofL (N op u x ++ N op u y)
    else [.Apply (.Apply g x) y]
  | t => if t = .Boolean u then [] else [t]

/-- No operand is stuck. -/
def Good (op : UserOp) : Term → Prop
  | .Apply (.Apply g x) y => g ≠ .Stuck ∧ (g = .UOp op → Good op x ∧ Good op y)
  | t => t ≠ .Stuck

/-- `op` is `and` or `or`, with its unit. -/
structure IsOp (op : UserOp) (u : Bool) : Prop where
  isNil : __eo_is_list_nil (.UOp op) (.Boolean u) = .Boolean true
  notNil : ∀ g x y, __eo_is_list_nil (.UOp op) (.Apply (.Apply g x) y) = .Boolean false
  nil : ∀ T, T ≠ .Stuck → __eo_nil (.UOp op) T = .Boolean u

theorem isOp_and : IsOp .and true := by
  refine ⟨rfl, fun _ _ _ => rfl, fun T hT => ?_⟩
  cases T <;> first | rfl | exact absurd rfl hT

theorem isOp_or : IsOp .or false := by
  refine ⟨rfl, fun _ _ _ => rfl, fun T hT => ?_⟩
  cases T <;> first | rfl | exact absurd rfl hT

theorem mem_setofL {l : List Term} {y : Term} : y ∈ setofL l ↔ y ∈ l := by
  induction l with
  | nil => simp [setofL]
  | cons x l ih =>
    simp only [setofL, List.mem_cons, List.mem_filter, ih, decide_eq_true_eq]
    by_cases h : y = x <;> simp [h]

theorem nodup_setofL (l : List Term) : (setofL l).Nodup := by
  induction l with
  | nil => simp [setofL]
  | cons x l ih =>
    simp only [setofL, List.nodup_cons, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2 rfl, ih.filter _⟩

theorem mk_apply {a b : Term} (ha : a ≠ .Stuck) (hb : b ≠ .Stuck) : __eo_mk_apply a b = .Apply a b := by
  unfold __eo_mk_apply
  split <;> simp_all

theorem eo_eq {a b : Term} (ha : a ≠ .Stuck) (hb : b ≠ .Stuck) : __eo_eq a b = .Boolean (decide (b = a)) := by
  unfold __eo_eq
  split <;> simp_all [native_teq]

theorem eo_ite_true (a b : Term) : __eo_ite (.Boolean true) a b = a := by simp [native_ite, native_teq]
theorem eo_ite_false (a b : Term) : __eo_ite (.Boolean false) a b = b := by simp [native_ite, native_teq]

theorem requires_true (a : Term) : __eo_requires (.Boolean true) (.Boolean true) a = a := by
  simp [__eo_requires, native_ite, native_teq, native_not]

variable {op : UserOp} {u : Bool}

theorem chain_cons (x : Term) (l : List Term) :
    chain op u (x :: l) = .Apply (.Apply (.UOp op) x) (chain op u l) := rfl

theorem chain_ne (l : List Term) : chain op u l ≠ .Stuck := by
  cases l <;> simp [chain, eoRightAssocNil, eoApp2]

theorem get_nil (h : IsOp op u) (l : List Term) : __eo_get_nil_rec (.UOp op) (chain op u l) = .Boolean u := by
  induction l with
  | nil =>
    show __eo_requires (__eo_is_list_nil (.UOp op) (.Boolean u)) (.Boolean true) (.Boolean u) = _
    rw [h.isNil, requires_true]
  | cons x l ih =>
    show __eo_requires (.UOp op) (.UOp op) (__eo_get_nil_rec (.UOp op) (chain op u l)) = _
    rw [ih]; simp [__eo_requires, native_ite, native_teq, native_not]

theorem is_list (h : IsOp op u) (l : List Term) : __eo_is_list (.UOp op) (chain op u l) = .Boolean true := by
  have : __eo_is_list (.UOp op) (chain op u l) = __eo_is_ok (__eo_get_nil_rec (.UOp op) (chain op u l)) := by
    have hc := chain_ne (op := op) (u := u) l
    unfold __eo_is_list
    split <;> simp_all
  rw [this, get_nil h]
  simp [__eo_is_ok, native_teq, native_not]

theorem concat_rec (l r : List Term) :
    __eo_list_concat_rec (chain op u l) (chain op u r) = chain op u (l ++ r) := by
  induction l with
  | nil =>
    have hr := chain_ne (op := op) (u := u) r
    show __eo_list_concat_rec (.Boolean u) (chain op u r) = chain op u r
    unfold __eo_list_concat_rec
    split <;> simp_all
  | cons x l ih =>
    have hr := chain_ne (op := op) (u := u) r
    rw [chain_cons, List.cons_append, chain_cons, ← ih]
    have : __eo_list_concat_rec (.Apply (.Apply (.UOp op) x) (chain op u l)) (chain op u r) =
        __eo_mk_apply (.Apply (.UOp op) x) (__eo_list_concat_rec (chain op u l) (chain op u r)) := by
      rw [__eo_list_concat_rec]; exact hr
    rw [this, ih, mk_apply (by simp) (chain_ne _)]

theorem erase_all_rec {z : Term} (hz : z ≠ .Stuck) (l : List Term) (hl : ∀ x ∈ l, x ≠ .Stuck) :
    __eo_list_erase_all_rec (chain op u l) z = chain op u (l.filter fun y => decide (y ≠ z)) := by
  induction l with
  | nil =>
    show __eo_list_erase_all_rec (.Boolean u) z = .Boolean u
    unfold __eo_list_erase_all_rec
    split <;> simp_all
  | cons x l ih =>
    have hx := hl x (by simp)
    have : __eo_list_erase_all_rec (.Apply (.Apply (.UOp op) x) (chain op u l)) z =
        __eo_prepend_if (__eo_not (__eo_eq z x)) (.UOp op) x (__eo_list_erase_all_rec (chain op u l) z) := by
      rw [__eo_list_erase_all_rec]; exact hz
    rw [chain_cons, this, ih (fun y hy => hl y (by simp [hy])), eo_eq hz hx]
    have hc := chain_ne (op := op) (u := u) (l.filter fun y => decide (y ≠ z))
    by_cases e : x = z
    · subst e
      rw [show __eo_not (.Boolean (decide (x = x))) = .Boolean false by simp [__eo_not, native_not],
        List.filter_cons_of_neg (by simp)]
      unfold __eo_prepend_if
      split <;> simp_all
    · rw [show __eo_not (.Boolean (decide (x = z))) = .Boolean true by simp [__eo_not, native_not, e],
        List.filter_cons_of_pos (by simp [e]), chain_cons]
      unfold __eo_prepend_if
      split <;> simp_all

theorem setof_rec (l : List Term) (hl : ∀ x ∈ l, x ≠ .Stuck) :
    __eo_list_setof_rec (chain op u l) = chain op u (setofL l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show __eo_mk_apply (.Apply (.UOp op) x) (__eo_list_erase_all_rec (__eo_list_setof_rec (chain op u l)) x) = _
    rw [ih (fun y hy => hl y (by simp [hy])), erase_all_rec (hl x (by simp)) _
      (fun y hy => hl y (by simp [mem_setofL.mp hy])), mk_apply (by simp) (chain_ne _)]
    rfl

theorem setof (h : IsOp op u) (l : List Term) (hl : ∀ x ∈ l, x ≠ .Stuck) :
    __eo_list_setof (.UOp op) (chain op u l) = chain op u (setofL l) := by
  rw [__eo_list_setof, is_list h, requires_true, setof_rec l hl]

/-- An operand. -/
theorem leaf {t : Term} (ht : t ≠ .Stuck) (he : t ≠ .Boolean u) :
    __eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) t = chain op u [t] := by
  have : __eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) t =
      __eo_ite (__eo_eq (.Boolean u) t) (.Boolean u) (__eo_l_2___get_ai_norm_rec (.UOp op) (.Boolean u) t) := by
    rw [__eo_l_1___get_ai_norm_rec] <;> simp_all
  rw [this, eo_eq (by simp) ht, decide_eq_false he, eo_ite_false]
  rw [__eo_l_2___get_ai_norm_rec] <;> simp_all [chain, eoRightAssocNil, eoApp2]

/-- **Logos's normal form is the list of the operands.** -/
theorem rec_eq (h : IsOp op u) : ∀ {t : Term}, Good op t →
    __get_ai_norm_rec (.UOp op) (.Boolean u) t = chain op u (N op u t) ∧ ∀ x ∈ N op u t, x ≠ .Stuck := by
  intro t
  fun_induction N op u t with
  | case1 x y ihx ihy =>
    intro hg
    obtain ⟨hx, hy⟩ := hg.2 rfl
    obtain ⟨ex, nx⟩ := ihx hx
    obtain ⟨ey, ny⟩ := ihy hy
    have hs : ∀ z ∈ N op u x ++ N op u y, z ≠ Term.Stuck := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact nx z hz
      · exact ny z hz
    refine ⟨?_, fun z hz => hs z (mem_setofL.mp hz)⟩
    have : __get_ai_norm_rec (.UOp op) (.Boolean u) (.Apply (.Apply (.UOp op) x) y) =
        __eo_ite (__eo_eq (.UOp op) (.UOp op)) (__eo_list_setof (.UOp op) (__eo_list_concat (.UOp op)
          (__get_ai_norm_rec (.UOp op) (.Boolean u) x) (__get_ai_norm_rec (.UOp op) (.Boolean u) y)))
          (__eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) (.Apply (.Apply (.UOp op) x) y)) := by
      rw [__get_ai_norm_rec] <;> simp
    rw [this, eo_eq (by simp) (by simp), decide_eq_true rfl, eo_ite_true, ex, ey, __eo_list_concat, is_list h, is_list h,
      requires_true, requires_true, concat_rec, setof h _ hs]
  | case2 g x y hne =>
    intro hg
    refine ⟨?_, by simp⟩
    have : __get_ai_norm_rec (.UOp op) (.Boolean u) (.Apply (.Apply g x) y) =
        __eo_ite (__eo_eq (.UOp op) g) (__eo_list_setof (.UOp op) (__eo_list_concat (.UOp op)
          (__get_ai_norm_rec (.UOp op) (.Boolean u) x) (__get_ai_norm_rec (.UOp op) (.Boolean u) y)))
          (__eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) (.Apply (.Apply g x) y)) := by
      rw [__get_ai_norm_rec] <;> simp
    rw [this, eo_eq (by simp) hg.1, decide_eq_false hne, eo_ite_false]
    exact leaf (by simp) (by simp)
  | case3 =>
    intro _
    refine ⟨?_, by simp⟩
    have : __get_ai_norm_rec (.UOp op) (.Boolean u) (.Boolean u) =
        __eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) (.Boolean u) := by
      rw [__get_ai_norm_rec] <;> simp
    rw [this]
    have : __eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) (.Boolean u) =
        __eo_ite (__eo_eq (.Boolean u) (.Boolean u)) (.Boolean u)
          (__eo_l_2___get_ai_norm_rec (.UOp op) (.Boolean u) (.Boolean u)) := by
      rw [__eo_l_1___get_ai_norm_rec] <;> simp
    rw [this, eo_eq (by simp) (by simp), decide_eq_true rfl, eo_ite_true]
    rfl
  | case4 t hn he =>
    intro hg
    have hs : t ≠ .Stuck := by
      unfold Good at hg
      split at hg
      · simp
      · exact hg
    refine ⟨?_, by simpa using hs⟩
    have : __get_ai_norm_rec (.UOp op) (.Boolean u) t = __eo_l_1___get_ai_norm_rec (.UOp op) (.Boolean u) t := by
      unfold __get_ai_norm_rec
      split <;> simp_all
    rw [this]
    exact leaf hs he

/-! ## Comparing normal forms -/

theorem get_elements (l : List Term) (hl : ∀ x ∈ l, x ≠ .Stuck) :
    __eo_get_elements_rec (chain op u l) = eoList l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show __eo_mk_apply (.Apply .__eo_List_cons x) (__eo_get_elements_rec (chain op u l)) = _
    have : eoList l ≠ .Stuck := by cases l <;> simp [eoList]
    rw [ih (fun y hy => hl y (by simp [hy])), mk_apply (by simp) this]
    rfl

theorem eoList_ne (l : List Term) : eoList l ≠ .Stuck := by cases l <;> simp [eoList]

theorem eoList_inj : ∀ {l r : List Term}, eoList l = eoList r → l = r
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eoList] at h
  | _ :: _, [], h => by simp [eoList] at h
  | a :: l, b :: r, h => by
    simp only [eoList, Term.Apply.injEq, true_and] at h
    rw [h.1, eoList_inj h.2]

theorem erase_rec {z : Term} (hz : z ≠ .Stuck) (l : List Term) (hl : ∀ x ∈ l, x ≠ .Stuck) :
    __eo_list_erase_rec (eoList l) z = eoList (eraseL l z) := by
  induction l with
  | nil =>
    show __eo_list_erase_rec .__eo_List_nil z = _
    unfold __eo_list_erase_rec
    split <;> simp_all [eraseL, eoList]
  | cons x l ih =>
    have : __eo_list_erase_rec (.Apply (.Apply .__eo_List_cons x) (eoList l)) z =
        __eo_ite (__eo_eq x z) (eoList l) (__eo_mk_apply (.Apply .__eo_List_cons x) (__eo_list_erase_rec (eoList l) z)) := by
      rw [__eo_list_erase_rec]; exact hz
    rw [eoList, this, eo_eq (hl x (by simp)) hz, ih (fun y hy => hl y (by simp [hy])), eraseL]
    by_cases e : x = z
    · rw [decide_eq_true e.symm, eo_ite_true, ite_eq_left e]
    · rw [decide_eq_false (Ne.symm e), eo_ite_false, ite_eq_right e, mk_apply (by simp) (eoList_ne _)]
      rfl

theorem length_eraseL {l : List Term} {z : Term} (h : z ∈ l) : (eraseL l z).length + 1 = l.length := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    rw [eraseL]
    split
    · simp
    · rename_i hne
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hne
      · simp [ih h]

theorem mem_eraseL {l : List Term} {y z : Term} (h : y ∈ l) (hne : y ≠ z) : y ∈ eraseL l z := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    rw [eraseL]
    split
    · rename_i e
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd e hne
      · exact h
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · simp [ih h]

theorem of_mem_eraseL {l : List Term} {y z : Term} (h : y ∈ eraseL l z) : y ∈ l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    rw [eraseL] at h
    split at h
    · simp [h]
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · simp [ih h]

theorem minclude (ys : List Term) : ∀ xs : List Term, (∀ x ∈ xs, x ≠ .Stuck) → ys.Nodup → (∀ y ∈ ys, y ∈ xs) →
    __eo_list_minclude_rec (eoList xs) (eoList ys) (.Boolean true) = .Boolean true := by
  induction ys with
  | nil =>
    intro xs _ _ _
    have := eoList_ne xs
    show __eo_list_minclude_rec (eoList xs) .__eo_List_nil (.Boolean true) = _
    rw [__eo_list_minclude_rec]; exact this
  | cons y ys ih =>
    intro xs hx hn hs
    have hy : y ∈ xs := hs y (by simp)
    have hyS := hx y hy
    have hrw : __eo_list_minclude_rec (eoList xs) (.Apply (.Apply .__eo_List_cons y) (eoList ys)) (.Boolean true) =
        __eo_list_minclude_rec (__eo_list_erase_rec (eoList xs) y) (eoList ys)
          (__eo_not (__eo_eq (__eo_list_erase_rec (eoList xs) y) (eoList xs))) := by
      rw [__eo_list_minclude_rec]; exact eoList_ne xs
    rw [eoList, hrw, erase_rec hyS xs hx, eo_eq (eoList_ne _) (eoList_ne _)]
    have hne : eoList xs ≠ eoList (eraseL xs y) := by
      intro e
      have e := congrArg List.length (eoList_inj e)
      have := length_eraseL hy
      omega
    rw [decide_eq_false hne, show __eo_not (.Boolean false) = .Boolean true from rfl]
    rw [List.nodup_cons] at hn
    refine ih _ (fun x h => hx x (of_mem_eraseL h)) hn.2 fun z hz => ?_
    exact mem_eraseL (hs z (by simp [hz])) fun e => hn.1 (e ▸ hz)

theorem meq (h : IsOp op u) {l r : List Term} (hl : ∀ x ∈ l, x ≠ .Stuck) (nl : l.Nodup) (nr : r.Nodup)
    (hlr : ∀ x, x ∈ l ↔ x ∈ r) :
    __eo_list_meq (.UOp op) (chain op u l) (chain op u r) = .Boolean true := by
  have hr : ∀ x ∈ r, x ≠ Term.Stuck := fun x hx => hl x ((hlr x).mpr hx)
  simp only [__eo_list_meq]
  rw [is_list h, is_list h, requires_true, requires_true, get_elements l hl, get_elements r hr,
    minclude r l hl nr fun y hy => (hlr y).mpr hy, minclude l r hr nl fun y hy => (hlr y).mp hy]
  rfl

/-- The normal form of an operand list: the unit, the operand, or the list. -/
def form (op : UserOp) (u : Bool) : List Term → Term
  | [x] => x
  | l => chain op u l

theorem form_ne {l : List Term} (hl : ∀ x ∈ l, x ≠ .Stuck) : form op u l ≠ .Stuck := by
  unfold form
  split
  · exact hl _ (by simp)
  · exact chain_ne _

/-- `@@aci_sorted f t`. -/
def sorted (op : UserOp) (t : Term) : Term := .Apply (.Apply (.UOp ._at__at_aci_sorted) (.UOp op)) t

theorem get_ai (h : IsOp op u) {x y : Term} (hg : Good op (.Apply (.Apply (.UOp op) x) y))
    (ht : __eo_typeof (.Apply (.Apply (.UOp op) x) y) ≠ .Stuck) :
    __get_ai_norm (.Apply (.Apply (.UOp op) x) y) = form op u (N op u (.Apply (.Apply (.UOp op) x) y)) := by
  rw [__get_ai_norm, h.nil _ ht, (rec_eq h hg).1, __eo_list_singleton_elim, is_list h, requires_true]
  generalize N op u _ = l
  match l with
  | [] => rfl
  | [x] =>
    show __eo_ite (__eo_is_list_nil (.UOp op) (.Boolean u)) x _ = _
    rw [h.isNil, eo_ite_true]; rfl
  | x :: y :: l =>
    show __eo_ite (__eo_is_list_nil (.UOp op) (.Apply (.Apply (.UOp op) y) (chain op u l))) x _ = _
    rw [h.notNil, eo_ite_false]; rfl

/-- The comparison of `@@aci_sorted f t` with `b`, which is `true` if `t` is
`b`, and not stuck. -/
theorem norm_eq_val {t b : Term} (ht : t ≠ .Stuck) (hb : b ≠ .Stuck) :
    __aci_norm_eq (sorted op t) b =
      if b = sorted op t ∨ b = t then .Boolean true else __eo_l_2___aci_norm_eq (sorted op t) b := by
  have h1 : __aci_norm_eq (sorted op t) b =
      __eo_ite (__eo_eq (sorted op t) b) (.Boolean true) (__eo_l_1___aci_norm_eq (sorted op t) b) := by
    rw [sorted, __aci_norm_eq] <;> simp_all
  have h2 : __eo_l_1___aci_norm_eq (sorted op t) b =
      __eo_ite (__eo_eq t b) (.Boolean true) (__eo_l_2___aci_norm_eq (sorted op t) b) := by
    rw [sorted, __eo_l_1___aci_norm_eq]; simp_all
  rw [h1, eo_eq (by simp [sorted]) hb, h2, eo_eq ht hb]
  by_cases e₁ : b = sorted op t
  · rw [decide_eq_true e₁, eo_ite_true, ite_eq_left (.inl e₁)]
  · rw [decide_eq_false e₁, eo_ite_false]
    by_cases e₂ : b = t
    · rw [decide_eq_true e₂, eo_ite_true, ite_eq_left (.inr e₂)]
    · rw [decide_eq_false e₂, eo_ite_false, ite_eq_right (by simp [e₁, e₂])]

/-- Against a term that is not `@@aci_sorted`, it is `true` or `false`. -/
theorem norm_eq_bool {t x y : Term} (hop : op ≠ ._at__at_aci_sorted) (ht : t ≠ .Stuck) :
    ∃ b, __aci_norm_eq (sorted op t) (.Apply (.Apply (.UOp op) x) y) = .Boolean b := by
  rw [norm_eq_val ht (by simp)]
  split
  · exact ⟨true, rfl⟩
  · refine ⟨false, ?_⟩
    rw [sorted]
    unfold __eo_l_2___aci_norm_eq
    split
    · simp_all
    · simp_all
    · simp_all
    · rw [__eo_l_3___aci_norm_eq] <;> simp

/-- The comparison of the normal forms of two terms with the same operands. -/
theorem norm_eq_sorted (h : IsOp op u) {l r : List Term} (hl : ∀ x ∈ l, x ≠ .Stuck) (nl : l.Nodup) (nr : r.Nodup)
    (hlr : ∀ x, x ∈ l ↔ x ∈ r) :
    __aci_norm_eq (sorted op (form op u l)) (sorted op (form op u r)) = .Boolean true := by
  have hr : ∀ x ∈ r, x ≠ Term.Stuck := fun x hx => hl x ((hlr x).mpr hx)
  rw [norm_eq_val (form_ne hl) (by simp [sorted])]
  split
  · rfl
  rename_i hne
  -- lists of at most one operand are equal
  have hp : l.Perm r := (List.perm_ext_iff_of_nodup nl nr).mpr hlr
  have hform : form op u l = chain op u l ∧ form op u r = chain op u r := by
    match l, r, hp with
    | [], r, hp =>
      rw [List.nil_perm] at hp; subst hp; exact ⟨rfl, rfl⟩
    | [x], r, hp =>
      rw [List.singleton_perm] at hp; subst hp
      exact absurd (Or.inl rfl) hne
    | x :: y :: l, r, hp =>
      have := hp.length_eq
      match r, this with
      | x' :: y' :: r, _ => exact ⟨rfl, rfl⟩
  rw [hform.1, hform.2, sorted, sorted]
  have : __eo_l_2___aci_norm_eq (.Apply (.Apply (.UOp ._at__at_aci_sorted) (.UOp op)) (chain op u l))
      (.Apply (.Apply (.UOp ._at__at_aci_sorted) (.UOp op)) (chain op u r)) =
      __eo_ite (__eo_eq (.UOp op) (.UOp op)) (__eo_list_meq (.UOp op) (chain op u l) (chain op u r))
        (__eo_l_3___aci_norm_eq (.Apply (.Apply (.UOp ._at__at_aci_sorted) (.UOp op)) (chain op u l))
          (.Apply (.Apply (.UOp ._at__at_aci_sorted) (.UOp op)) (chain op u r))) := by
    rw [__eo_l_2___aci_norm_eq]
  rw [this, eo_eq (by simp) (by simp), decide_eq_true rfl, eo_ite_true, meq h hl nl nr hlr]

theorem nodup_N (x y : Term) : (N op u (.Apply (.Apply (.UOp op) x) y)).Nodup := by
  rw [N, ite_eq_left rfl]; exact nodup_setofL _

theorem get_form (hop : op = .and ∨ op = .or) (x y : Term) :
    __get_aci_normal_form (.Apply (.Apply (.UOp op) x) y) =
      __eo_mk_apply (.Apply (.UOp ._at__at_aci_sorted) (.UOp op)) (__get_ai_norm (.Apply (.Apply (.UOp op) x) y)) := by
  rcases hop with rfl | rfl <;> rfl

/-- **`aci_norm` accepts two terms with the same operands.** -/
theorem prog (h : IsOp op u) (hop : op = .and ∨ op = .or) {x y b : Term}
    (ga : Good op (.Apply (.Apply (.UOp op) x) y)) (gb : Good op b)
    (ta : __eo_typeof (.Apply (.Apply (.UOp op) x) y) ≠ .Stuck) (tb : __eo_typeof b ≠ .Stuck)
    (hs : ∀ z, z ∈ N op u (.Apply (.Apply (.UOp op) x) y) ↔ z ∈ N op u b) :
    __eo_prog_aci_norm (eoApp2 UserOp.eq (.Apply (.Apply (.UOp op) x) y) b) =
      eoApp2 UserOp.eq (.Apply (.Apply (.UOp op) x) y) b := by
  have hopS : op ≠ ._at__at_aci_sorted := by rcases hop with rfl | rfl <;> simp
  have hla := (rec_eq h ga).2
  have hna := nodup_N (op := op) (u := u) x y
  have hfa : __get_aci_normal_form (.Apply (.Apply (.UOp op) x) y) =
      sorted op (form op u (N op u (.Apply (.Apply (.UOp op) x) y))) := by
    rw [get_form hop, get_ai h ga ta, mk_apply (by simp) (form_ne hla), sorted]
  show __eo_requires (__eo_ite (__aci_norm_eq (__get_aci_normal_form (.Apply (.Apply (.UOp op) x) y)) b) (.Boolean true)
    (__eo_ite (__aci_norm_eq (__get_aci_normal_form b) (.Apply (.Apply (.UOp op) x) y)) (.Boolean true)
      (__aci_norm_eq (__get_aci_normal_form (.Apply (.Apply (.UOp op) x) y)) (__get_aci_normal_form b)))) (.Boolean true) _ = _
  rw [hfa]
  by_cases hb : ∃ x' y', b = .Apply (.Apply (.UOp op) x') y'
  · obtain ⟨x', y', rfl⟩ := hb
    have hlb := (rec_eq h gb).2
    have hfb : __get_aci_normal_form (.Apply (.Apply (.UOp op) x') y') =
        sorted op (form op u (N op u (.Apply (.Apply (.UOp op) x') y'))) := by
      rw [get_form hop, get_ai h gb tb, mk_apply (by simp) (form_ne hlb), sorted]
    rw [hfb, norm_eq_sorted h hla hna (nodup_N x' y') hs]
    obtain ⟨b₁, e₁⟩ := norm_eq_bool (op := op) (x := x') (y := y') hopS (form_ne (op := op) (u := u) hla)
    obtain ⟨b₂, e₂⟩ := norm_eq_bool (op := op) (x := x) (y := y) hopS (form_ne (op := op) (u := u) hlb)
    rw [e₁, e₂]
    cases b₁ <;> cases b₂ <;> simp only [eo_ite_true, eo_ite_false, requires_true] <;> rfl
  · -- a single operand, or the unit
    have hNb : N op u b = if b = .Boolean u then [] else [b] := by
      unfold N
      split
      · rename_i g x' y'
        rw [ite_eq_right fun e => hb ⟨x', y', by rw [e]⟩, ite_eq_right (by simp)]
      · rfl
    have hbS : b ≠ .Stuck := by
      rintro rfl; exact absurd rfl gb
    have hf : form op u (N op u (.Apply (.Apply (.UOp op) x) y)) = b := by
      generalize N op u (.Apply (.Apply (.UOp op) x) y) = l at *
      rw [hNb] at hs
      split at hs
      · rename_i e
        have : l = [] := List.eq_nil_iff_forall_not_mem.mpr fun z hz => by simpa using (hs z).mp hz
        subst this; rw [e]; rfl
      · have hp : l.Perm [b] := (List.perm_ext_iff_of_nodup hna (by simp)).mpr hs
        rw [List.perm_singleton] at hp
        subst hp; rfl
    rw [hf, norm_eq_val hbS hbS, ite_eq_left (.inr rfl), eo_ite_true, requires_true]
    rfl

/-! ## The operands of a node -/

open Node (termTy)

theorem ty_op (hop : op = .and ∨ op = .or) (x y : Term) :
    termTy (.Apply (.Apply (.UOp op) x) y) = boolTy2 (termTy x) (termTy y) := by
  rcases hop with rfl | rfl
  · exact Node.termTy_and x y
  · exact Node.termTy_or x y

theorem boolTy2_ne {T U : SmtType} (h : boolTy2 T U ≠ .None) : T = .Bool ∧ U = .Bool := by
  unfold boolTy2 at h
  by_cases h1 : T = .Bool <;> by_cases h2 : U = .Bool <;> simp_all [native_ite, native_Teq]

theorem ty_stuck : termTy .Stuck = .None := by
  unfold Node.termTy
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl, __smtx_typeof.eq_def]

theorem ty_stuck_app (x y : Term) : termTy (.Apply (.Apply .Stuck x) y) = .None := by
  unfold Node.termTy
  rw [show __eo_to_smt (.Apply (.Apply .Stuck x) y) =
    SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) (__eo_to_smt y) from rfl]
  rw [__smtx_typeof.eq_def]
  dsimp only
  rw [__smtx_typeof.eq_def (SmtTerm.Apply SmtTerm.None _)]
  dsimp only
  rw [__smtx_typeof.eq_def SmtTerm.None]
  rfl

/-- A well-typed term has no stuck operand. -/
theorem good_of_ty (hop : op = .and ∨ op = .or) : ∀ t : Term, termTy t ≠ .None → Good op t := by
  intro t
  fun_induction Good op t with
  | case1 g x y ihx ihy =>
    intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h (ty_stuck_app x y)
    · rintro rfl
      rw [ty_op hop] at h
      obtain ⟨hx, hy⟩ := boolTy2_ne h
      exact ⟨ihx (by rw [hx]; simp), ihy (by rw [hy]; simp)⟩
  | case2 t ht =>
    intro h e
    subst e; exact h ty_stuck

theorem mem_N_chain (l : List Term) (z : Term) : z ∈ N op u (chain op u l) ↔ ∃ t ∈ l, z ∈ N op u t := by
  induction l with
  | nil =>
    show z ∈ N op u (.Boolean u) ↔ _
    simp [N]
  | cons x l ih =>
    rw [chain_cons, N, ite_eq_left rfl, mem_setofL, List.mem_append, ih]
    simp

/-- The kind and its operator. -/
structure KindOp (k : Kind) (op : UserOp) (u : Bool) : Prop where
  unit : Aci.unit? k = some u
  shape : k.eoShape = .rightAssocNil op (.const (.Boolean u))

theorem toEo_chain {k : Kind} (h : KindOp k op u) {cs : Array Node} (hs : 2 ≤ cs.size) :
    (Node.app (.kind k) cs).toEo = chain op u (cs.toList.map Node.toEo) := by
  rw [Node.toEo_app]
  simp only [Op.eoShape, h.shape, AppShape.toEo, List.length_map, Array.length_toList]
  rw [ite_eq_left hs]
  rfl

/-- **The operands of a node are those of its leaves.** -/
theorem mem_N_leaves {k : Kind} (h : KindOp k op u) (z : Term) : ∀ n : Node,
    z ∈ N op u n.toEo ↔ ∃ l ∈ Aci.leaves k u n, z ∈ N op u l.toEo
  | .const (.boolean b) => by
    rw [Aci.leaves]
    split
    · rename_i e
      subst e
      simp [Node.toEo, Const.toEo, N]
    · simp
  | .app (.kind k') cs => by
    rw [Aci.leaves]
    split
    · rename_i e
      obtain ⟨rfl, hs⟩ := e
      have ih : ∀ c ∈ cs.toList, (z ∈ N op u c.toEo ↔ ∃ l ∈ Aci.leaves k' u c, z ∈ N op u l.toEo) :=
        fun c hc => mem_N_leaves h z c
      rw [toEo_chain h hs, mem_N_chain]
      simp only [List.mem_map, List.mem_flatMap, Array.toList_attach, List.mem_attachWith]
      constructor
      · rintro ⟨_, ⟨c, hc, rfl⟩, hz⟩
        obtain ⟨l, hl, hz⟩ := (ih c hc).mp hz
        exact ⟨l, ⟨⟨c, by simpa using hc⟩, by simpa using hc, hl⟩, hz⟩
      · rintro ⟨l, ⟨⟨c, hc⟩, -, hl⟩, hz⟩
        have hc' : c ∈ cs.toList := by simpa using hc
        exact ⟨_, ⟨c, hc', rfl⟩, (ih c hc').mpr ⟨l, hl, hz⟩⟩
    · simp
  | .const (.integer _) | .const (.rational _) | .const (.string _) | .const (.bitVector ..) | .const (.emptySet _)
  | .const (.emptySeq _) | .const (.dtCons ..) | .const (.dtSel ..) | .var .. | .boundVar .. | .skolem ..
  | .app (.indexed ..) _ | .app (.node ..) _ => by
    rw [Aci.leaves] <;> simp
termination_by n => sizeOf n
decreasing_by all_goals (have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹_›); simp_all; omega)

end AciProof

open AciProof Node

theorem typeof_eq_inv {T U : SmtType} (h : __smtx_typeof_eq T U = .Bool) : T ≠ .None ∧ T = U := by
  unfold __smtx_typeof_eq __smtx_typeof_guard at h
  by_cases h1 : T = .None <;> by_cases h2 : T = U <;> simp_all [native_ite, native_Teq]

/-- **An `aci_norm` step on nodes with the same leaves is a CPC step.** -/
theorem aci_provesEq [LogosFacts] {n m : Node} (h : Aci.Ok n m) : ProvesEq (StaticProc.aciCmds n m) n m := by
  obtain ⟨hl, hty⟩ := h
  have hty' : __smtx_typeof (__eo_to_smt (eqFormula n m)) = SmtType.Bool := by
    rw [smtTypeF_eq] at hty
    rw [← Template.toEo_eq]; exact hty
  unfold Aci.LeavesOk at hl
  split at hl
  · rename_i k cs
    split at hl
    · rename_i u hu
      obtain ⟨hs, hmn, hnm⟩ := hl
      obtain ⟨op, hop, hk, hO⟩ : ∃ op, (op = UserOp.and ∨ op = .or) ∧ KindOp k op u ∧ IsOp op u := by
        unfold Aci.unit? at hu
        split at hu
        · obtain rfl := Option.some.inj hu
          exact ⟨.and, .inl rfl, ⟨rfl, rfl⟩, isOp_and⟩
        · obtain rfl := Option.some.inj hu
          exact ⟨.or, .inr rfl, ⟨rfl, rfl⟩, isOp_or⟩
        · cases hu
      obtain ⟨x, y, hn⟩ : ∃ x y, (Node.app (.kind k) cs).toEo = .Apply (.Apply (.UOp op) x) y := by
        rw [toEo_chain hk hs]
        match hcs : cs.toList with
        | [] => have := congrArg List.length hcs; rw [Array.length_toList] at this; simp only [List.length_nil] at this; omega
        | c :: l => exact ⟨c.toEo, _, rfl⟩
      rw [typeof_eqFormula] at hty'
      obtain ⟨hne, hEq⟩ := typeof_eq_inv hty'
      have hT : termTy (.Apply (.Apply (.UOp op) x) y) ≠ .None := by rw [← hn, termTy_toEo]; exact hne
      have hB : termTy (.Apply (.Apply (.UOp op) x) y) = .Bool := by
        rw [ty_op hop] at hT ⊢
        obtain ⟨h1, h2⟩ := boolTy2_ne hT
        rw [h1, h2]; rfl
      have hBm : termTy m.toEo = .Bool := by
        rw [termTy_toEo, ← hEq, ← termTy_toEo, hn]; exact hB
      have hstep := prog hO hop (good_of_ty hop _ hT) (good_of_ty hop m.toEo (by rw [hBm]; simp))
        (by rw [LogosFacts.eo_typeof_bool _ hB]; simp) (by rw [LogosFacts.eo_typeof_bool _ hBm]; simp)
        (fun z => by
          rw [← hn, mem_N_leaves hk z (.app (.kind k) cs), mem_N_leaves hk z m]
          exact ⟨fun ⟨l, hl, hz⟩ => ⟨l, hnm l hl, hz⟩, fun ⟨l, hl, hz⟩ => ⟨l, hmn l hl, hz⟩⟩)
      have hf : eqFormula (Node.app (.kind k) cs) m = eoApp2 UserOp.eq (.Apply (.Apply (.UOp op) x) y) m.toEo := by
        rw [eqFormula, hn]
      have hty'' : __smtx_typeof (__eo_to_smt (eqFormula (Node.app (.kind k) cs) m)) = SmtType.Bool := by
        rw [typeof_eqFormula]; exact hty'
      refine Template.provesEq_one ⟨by rw [eoHasSmtTranslation, hty'']; simp, trivial⟩ ?_ hty''
      show __eo_prog_aci_norm (eqFormula (Node.app (.kind k) cs) m) = _
      rw [hf]; exact hstep
    · exact hl.elim
  · exact hl.elim

end Telos
