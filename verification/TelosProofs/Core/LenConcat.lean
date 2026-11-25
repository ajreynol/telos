import TelosProofs.Core.Template
import Telos.Core.Static

/-!
# `str-len-concat-rec` steps on strings are CPC steps

`lenConcat_provesEq`: under `LenConcat.Ok`, Logos's checker accepts
`[str_len_concat_rec a b (str.++ cs… "")]`.
-/

open Eo Smtm SmtEval

set_option linter.internalConstructors false

namespace Telos

namespace LenConcat

open Node Template

theorem mk_apply {a b : Term} (ha : a ≠ .Stuck) (hb : b ≠ .Stuck) : __eo_mk_apply a b = .Apply a b := by
  unfold __eo_mk_apply
  split <;> simp_all

theorem requires_true (a : Term) : __eo_requires (.Boolean true) (.Boolean true) a = a := by
  simp [__eo_requires, native_ite, native_teq, native_not]

theorem requires_refl {x : Term} (hx : x ≠ .Stuck) (a : Term) : __eo_requires x x a = a := by
  simp [__eo_requires, native_ite, native_teq, native_not, hx]

theorem tail_ne (cs : List Node) : tail cs ≠ .Stuck := by
  cases cs <;> simp [tail, eoRightAssocNil, eoApp2]

theorem get_nil (cs : List Node) : __eo_get_nil_rec (.UOp .str_concat) (tail cs) = .String [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show __eo_requires (.UOp .str_concat) (.UOp .str_concat) (__eo_get_nil_rec (.UOp .str_concat) (tail cs)) = _
    rw [ih, requires_refl (by simp)]

theorem is_list (cs : List Node) : __eo_is_list (.UOp .str_concat) (tail cs) = .Boolean true := by
  have : __eo_is_list (.UOp .str_concat) (tail cs) = __eo_is_ok (__eo_get_nil_rec (.UOp .str_concat) (tail cs)) := by
    have hc := tail_ne cs
    unfold __eo_is_list
    split <;> simp_all
  rw [this, get_nil]
  rfl

theorem ty_tail {cs : List Node} (h : ∀ c ∈ cs, c.smtType = .Seq .Char) : termTy (tail cs) = .Seq .Char := by
  induction cs with
  | nil =>
    show termTy (Term.String []) = _
    rw [termTy_string]; rfl
  | cons c cs ih =>
    show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c.toEo) (tail cs)) = _
    rw [termTy_str_concat, ih (fun d hd => h d (by simp [hd])), termTy_toEo, h c (by simp)]
    rfl

/-- A concatenation of strings. -/
theorem toEo_concat {a b : Node} {cs : List Node} (ha : a.smtType = .Seq .Char) :
    (Node.app (.kind .STRING_CONCAT) ⟨a :: b :: cs⟩).toEo = tail (a :: b :: cs) := by
  rw [Node.toEo_app]
  show eoRightAssocNil .str_concat (typedNil .str_concat a.toEo) _ = _
  rw [typedNil_eq, termTy_toEo, ha]
  rfl

theorem toEo_len (a : Node) : (lenNode a).toEo = .Apply (.UOp .str_len) a.toEo := toEo_spine1 rfl a

theorem ty_len {a : Node} (h : a.smtType = .Seq .Char) : (lenNode a).smtType = .Int := by
  show termTy (lenNode a).toEo = _
  rw [toEo_len, termTy_str_len, termTy_toEo, h]; rfl

theorem ty_concat {a b : Node} {cs : List Node} (h : ∀ c ∈ a :: b :: cs, c.smtType = .Seq .Char) :
    (Node.app (.kind .STRING_CONCAT) ⟨a :: b :: cs⟩).smtType = .Seq .Char := by
  show termTy (Node.toEo _) = _
  rw [toEo_concat (h a (by simp)), ty_tail h]

theorem ty_concatOf {b : Node} {cs : List Node} (h : ∀ c ∈ b :: cs, c.smtType = .Seq .Char) :
    (concatOf b cs).smtType = .Seq .Char := by
  unfold concatOf
  cases cs with
  | nil => exact h b (by simp)
  | cons c cs => exact ty_concat h

/-- A sum of two integers. -/
theorem toEo_add {a b : Node} (ha : a.smtType = .Int) :
    (Node.app (.kind .ADD) #[a, b]).toEo = .Apply (.Apply (.UOp .plus) a.toEo)
      (.Apply (.Apply (.UOp .plus) b.toEo) (.Numeral 0)) := by
  rw [Node.toEo_app]
  show eoRightAssocNil .plus (typedNil .plus a.toEo) _ = _
  rw [typedNil_eq, termTy_toEo, ha]
  rfl

theorem singleton {b : Node} {cs : List Node} (hb : b.smtType = .Seq .Char) :
    __eo_list_singleton_elim (.UOp .str_concat) (.Apply (.Apply (.UOp .str_concat) b.toEo) (tail cs)) =
      (concatOf b cs).toEo := by
  rw [__eo_list_singleton_elim, show Term.Apply (.Apply (.UOp .str_concat) b.toEo) (tail cs) = tail (b :: cs) from rfl,
    is_list, requires_true]
  cases cs with
  | nil =>
    show __eo_ite (__eo_is_list_nil (.UOp .str_concat) (.String [])) b.toEo _ = _
    rw [show __eo_is_list_nil (.UOp .str_concat) (.String []) = .Boolean true from rfl]
    simp [native_ite, native_teq, concatOf]
  | cons c cs =>
    show __eo_ite (__eo_is_list_nil (.UOp .str_concat) (tail (c :: cs))) b.toEo (tail (b :: c :: cs)) = _
    rw [show __eo_is_list_nil (.UOp .str_concat) (tail (c :: cs)) = .Boolean false from rfl]
    rw [show concatOf b (c :: cs) = Node.app (.kind .STRING_CONCAT) ⟨b :: c :: cs⟩ from rfl, toEo_concat hb]
    simp [native_ite, native_teq]

end LenConcat

open LenConcat Node Template

/-- **A `str-len-concat-rec` step on strings is a CPC step.** -/
theorem lenConcat_provesEq [LogosFacts] {a b : Node} {cs : List Node} {n m : Node} (h : LenConcat.Ok a b cs n m) :
    ProvesEq (LenConcat.cmds a b cs) n m := by
  obtain ⟨rfl, rfl, hs⟩ := h
  have hs : ∀ x ∈ a :: b :: cs, x.smtType = .Seq .Char := fun x hx => by
    have := hs x hx; rwa [smtTypeF_eq] at this
  have ha := hs a (by simp)
  have hb := hs b (by simp)
  have hok : ∀ x ∈ [a, b], x.smtTypeF ≠ .None := fun x hx => by
    rw [smtTypeF_eq]
    rcases (by simpa using hx : x = a ∨ x = b) with rfl | rfl
    · rw [ha]; simp
    · rw [hb]; simp
  have hcs : ∀ x ∈ cs, x.smtType = .Seq .Char := fun x hx => hs x (by simp [hx])
  have haS := toEo_ne_stuck (hok a (by simp))
  have hbS := toEo_ne_stuck (hok b (by simp))
  have hcS := toEo_ne_stuck (a := concatOf b cs) (by
    rw [smtTypeF_eq, ty_concatOf fun x hx => hs x (by simp at hx ⊢; exact .inr hx)]; simp)
  have hsum : (rhs a b cs).toEo = .Apply (.Apply (.UOp .plus) (.Apply (.UOp .str_len) a.toEo))
      (.Apply (.Apply (.UOp .plus) (.Apply (.UOp .str_len) (concatOf b cs).toEo)) (.Numeral 0)) := by
    rw [rhs, toEo_add (ty_len ha), toEo_len, toEo_len]
  have hlhs : (lhs a b cs).toEo = .Apply (.UOp .str_len) (.Apply (.Apply (.UOp .str_concat) a.toEo)
      (.Apply (.Apply (.UOp .str_concat) b.toEo) (tail cs))) := by
    rw [lhs, toEo_len, toEo_concat ha]; rfl
  have hlT : (lhs a b cs).smtType = .Int := ty_len (ty_concat hs)
  have hrT : (rhs a b cs).smtType = .Int := by
    show termTy (rhs a b cs).toEo = _
    have hc := ty_concatOf (b := b) (cs := cs) fun x hx => hs x (by simp at hx ⊢; exact .inr hx)
    rw [hsum]
    rw [termTy_plus, termTy_plus, termTy_str_len, termTy_str_len, termTy_toEo, termTy_toEo, ha, hc]
    rw [show termTy (.Numeral 0) = .Int from (by unfold Node.termTy; rw [show __eo_to_smt (Term.Numeral 0) = SmtTerm.Numeral 0 from rfl, __smtx_typeof.eq_def])]
    rfl
  have hty : __smtx_typeof (__eo_to_smt (eqFormula (lhs a b cs) (rhs a b cs))) = SmtType.Bool := by
    rw [typeof_eqFormula, hlT, hrT]; rfl
  have tr : ∀ t : Term, termTy t = .Seq .Char → eoHasSmtTranslation t := fun t ht => by
    show termTy t ≠ .None
    rw [ht]; simp
  refine provesEq_one ⟨tr _ ha, tr _ hb, tr _ (ty_tail hcs), trivial⟩ ?_ hty
  show __eo_prog_str_len_concat_rec a.toEo b.toEo (tail cs) = _
  have hT := tail_ne cs
  have hrw : __eo_prog_str_len_concat_rec a.toEo b.toEo (tail cs) =
      __eo_mk_apply (.Apply (.UOp .eq) (.Apply (.UOp .str_len) (.Apply (.Apply (.UOp .str_concat) a.toEo)
        (.Apply (.Apply (.UOp .str_concat) b.toEo) (tail cs)))))
      (__eo_mk_apply (.Apply (.UOp .plus) (.Apply (.UOp .str_len) a.toEo))
        (__eo_mk_apply (__eo_mk_apply (.UOp .plus) (__eo_mk_apply (.UOp .str_len)
          (__eo_list_singleton_elim (.UOp .str_concat) (.Apply (.Apply (.UOp .str_concat) b.toEo) (tail cs)))))
          (.Numeral 0))) := by
    rw [__eo_prog_str_len_concat_rec] <;> assumption
  rw [hrw, singleton hb, mk_apply (a := .UOp .str_len) (by simp) hcS, eqFormula, hlhs, hsum]
  rfl

end Telos
