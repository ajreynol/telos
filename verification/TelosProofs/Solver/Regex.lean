import Cpc.SmtModel
import Telos.Solver.Regex

/-!
# The regular expressions of models are Logos's

A regular expression of a model (`TRe`, `Telos/Solver/Regex.lean`) has a Logos
value (`TRe.toS`): the same shape, with each character the Logos character of
its clamped code point. Each operation of telos's is the image of Logos's:
the simplifying constructors, the derivative, nullability, and membership
(`inRe_toS`). The value is canonical (`toS_canonical`), as a model's values
are.
-/

open Smtm SmtEval

namespace Telos.Solver.TRe

/-- The Logos character of a code point, clamped. -/
def chS (c : Nat) : SmtValue := .Char (reClamp c)

/-- The Logos value of a regular expression. -/
def toS : TRe → SmtRegLan
  | .empty => .empty
  | .epsilon => .epsilon
  | .char c => .char (chS c)
  | .range lo hi => .range (chS lo) (chS hi)
  | .allchar => .allchar
  | .concat r₁ r₂ => .concat (toS r₁) (toS r₂)
  | .union r₁ r₂ => .union (toS r₁) (toS r₂)
  | .inter r₁ r₂ => .inter (toS r₁) (toS r₂)
  | .star r => .star (toS r)
  | .comp r => .comp (toS r)

theorem clamp_valid (c : Nat) : native_char_valid (reClamp c) = true := by
  unfold reClamp native_char_valid
  split <;> simp_all

theorem clamp_clamp (c : Nat) : reClamp (reClamp c) = reClamp c := by
  unfold reClamp; split <;> simp_all

theorem ceq_iff : ∀ a b : TRe, ceq a b = true ↔ toS a = toS b := by
  intro a
  induction a with
  | concat a₁ a₂ ih₁ ih₂ | union a₁ a₂ ih₁ ih₂ | inter a₁ a₂ ih₁ ih₂ =>
    intro b; cases b <;> simp [ceq, toS, ih₁, ih₂]
  | star a ih | comp a ih => intro b; cases b <;> simp [ceq, toS, ih]
  | _ => intro b; cases b <;> simp [ceq, toS, chS]

theorem toS_empty_iff (a : TRe) : toS a = .empty ↔ a = .empty := by
  cases a <;> simp [toS]

theorem toS_epsilon_iff (a : TRe) : toS a = .epsilon ↔ a = .epsilon := by
  cases a <;> simp [toS]

theorem toS_comp_iff (a : TRe) (s : SmtRegLan) : toS a = .comp s ↔ ∃ b, a = .comp b ∧ toS b = s := by
  cases a <;> simp [toS]

theorem toS_star_iff (a : TRe) (s : SmtRegLan) : toS a = .star s ↔ ∃ b, a = .star b ∧ toS b = s := by
  cases a <;> simp [toS]

theorem nullable_toS : ∀ r : TRe, native_re_nullable (toS r) = nullable r := by
  intro r
  induction r with
  | concat _ _ ih₁ ih₂ | union _ _ ih₁ ih₂ | inter _ _ ih₁ ih₂ => simp [toS, native_re_nullable, nullable, ih₁, ih₂]
  | star _ ih | comp _ ih => simp [toS, native_re_nullable, nullable, ih]
  | _ => rfl

theorem mkConcat_toS (a b : TRe) : toS (mkConcat a b) = native_re_concat (toS a) (toS b) := by
  cases a <;> cases b <;> rfl

theorem mkUnion_toS (a b : TRe) : toS (mkUnion a b) = native_re_union (toS a) (toS b) := by
  cases a <;> cases b <;> simp only [mkUnion, native_re_union, toS] <;>
    first
    | rfl
    | (split <;> rename_i h <;> rw [ceq_iff] at h <;> simp only [toS] at h <;> simp [h, toS])

theorem mkInter_toS (a b : TRe) : toS (mkInter a b) = native_re_inter (toS a) (toS b) := by
  cases a <;> cases b <;> simp only [mkInter, native_re_inter, toS] <;>
    first
    | rfl
    | (split <;> rename_i h <;> rw [ceq_iff] at h <;> simp only [toS] at h <;> simp [h, toS])

theorem mkComp_toS (a : TRe) : toS (mkComp a) = native_re_comp (toS a) := by
  cases a <;> rfl

theorem mkStar_toS (a : TRe) : toS (mkStar a) = native_re_mult (toS a) := by
  cases a <;> rfl

/-- The derivative by a valid character. -/
theorem deriv_toS (c : Nat) (hc : reClamp c = c) :
    ∀ r : TRe, toS (deriv c r) = native_re_deriv (.Char c) (toS r) := by
  have hv : native_char_valid c = true := hc ▸ clamp_valid c
  intro r
  induction r with
  | empty | epsilon => rfl
  | char d =>
    simp only [deriv, toS, native_re_deriv, chS, SmtValue.Char.injEq, beq_iff_eq]
    split <;> rfl
  | range lo hi =>
    simp only [deriv, toS, native_re_deriv, chS, native_re_elem_valid, hv, clamp_valid,
      impl_native_re_elem_le, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    split <;> rfl
  | allchar => simp [deriv, toS, native_re_deriv, native_re_elem_valid, hv]
  | concat r₁ r₂ ih₁ ih₂ =>
    simp only [deriv, toS, native_re_deriv, mkUnion_toS, mkConcat_toS, ih₁, nullable_toS]
    split <;> simp [ih₂, toS]
  | union r₁ r₂ ih₁ ih₂ => simp only [deriv, toS, native_re_deriv, mkUnion_toS, ih₁, ih₂]
  | inter r₁ r₂ ih₁ ih₂ => simp only [deriv, toS, native_re_deriv, mkInter_toS, ih₁, ih₂]
  | star r ih => simp only [deriv, toS, native_re_deriv, mkConcat_toS, ih]
  | comp r ih => simp only [deriv, toS, native_re_deriv, mkComp_toS, ih]

/-- **Membership is Logos's**, of the string of the clamped code points. -/
theorem inRe_toS (w : List Nat) (r : TRe) :
    native_str_in_re ((w.map reClamp).map SmtValue.Char) (toS r) = inRe w r := by
  have hvalid : native_re_str_valid ((w.map reClamp).map SmtValue.Char) = true := by
    simp [native_re_str_valid, native_re_elem_valid, clamp_valid]
  simp only [native_str_in_re, hvalid, ↓reduceIte, inRe]
  rw [← nullable_toS]
  congr 1
  clear hvalid
  induction w generalizing r with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih, deriv_toS _ (clamp_clamp c)]

theorem ofList_toS : ∀ w : List Nat,
    toS (ofList w) = native_str_to_re ((w.map reClamp).map SmtValue.Char)
  | [] => rfl
  | c :: w => by
    simp only [ofList, native_str_to_re, List.map_cons, impl_native_re_of_list, mkConcat_toS]
    rw [ofList_toS w]
    rfl

theorem mkRange_toS (a b : List Nat) :
    toS (mkRange a b) = native_re_range ((a.map reClamp).map SmtValue.Char) ((b.map reClamp).map SmtValue.Char) := by
  match a, b with
  | [x], [y] => rfl
  | [], _ | _ :: _ :: _, _ => rfl
  | [_], [] | [_], _ :: _ :: _ => rfl

theorem toS_canonical : ∀ r : TRe, __smtx_re_canonical (toS r) = true := by
  intro r
  induction r with
  | concat _ _ ih₁ ih₂ | union _ _ ih₁ ih₂ | inter _ _ ih₁ ih₂ => simp [toS, __smtx_re_canonical, ih₁, ih₂, native_and]
  | star _ ih | comp _ ih => simp [toS, __smtx_re_canonical, ih]
  | char c => simp [toS, __smtx_re_canonical, chS, native_re_elem_valid, clamp_valid]
  | range lo hi => simp [toS, __smtx_re_canonical, chS, native_re_elem_valid, clamp_valid, native_and]
  | _ => rfl

end Telos.Solver.TRe
