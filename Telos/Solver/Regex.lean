/-!
# Regular expressions of models

The values of regular expressions in a model, and membership of a string in
one, for the model checker (`Model.ev` of `str.in_re`).

A value (`TRe`) is shaped as Logos's (`SmtRegLan`), with characters as code
points; its operations are Logos's, step for step: the same simplifying
constructors (`native_re_concat`, `native_re_union`, …), and membership by
Brzozowski derivatives (`native_re_deriv`, `native_re_nullable`,
`native_str_in_re`). So each is the image of Logos's under the map of values
(`verification/TelosProofs/Solver/Regex.lean`), and telos does not run Logos's.

A character is compared as its Logos value is: clamped to a valid code point
(`clamp`, as `MVal.clampChar`), so that equal values are those with equal
images (`ceq`).
-/

namespace Telos.Solver

/-- A character as Logos has it: one that is not valid is `0`. -/
def reClamp (c : Nat) : Nat := if c < 196608 then c else 0

/-- A regular expression of a model (Logos's `SmtRegLan`). -/
inductive TRe where
  | empty
  | epsilon
  | char (c : Nat)
  | range (lo hi : Nat)
  | allchar
  | concat (r₁ r₂ : TRe)
  | union (r₁ r₂ : TRe)
  | inter (r₁ r₂ : TRe)
  | star (r : TRe)
  | comp (r : TRe)
  deriving DecidableEq, Inhabited, Repr

namespace TRe

/-- Equality of the Logos values (characters clamped). -/
def ceq : TRe → TRe → Bool
  | .empty, .empty | .epsilon, .epsilon | .allchar, .allchar => true
  | .char c, .char d => reClamp c == reClamp d
  | .range a b, .range c d => reClamp a == reClamp c && reClamp b == reClamp d
  | .concat a b, .concat c d | .union a b, .union c d | .inter a b, .inter c d => ceq a c && ceq b d
  | .star a, .star b | .comp a, .comp b => ceq a b
  | _, _ => false

/-- `native_re_nullable`. -/
def nullable : TRe → Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .range _ _ => false
  | .allchar => false
  | .concat r₁ r₂ => nullable r₁ && nullable r₂
  | .union r₁ r₂ => nullable r₁ || nullable r₂
  | .inter r₁ r₂ => nullable r₁ && nullable r₂
  | .star _ => true
  | .comp r => !(nullable r)

/-- `native_re_concat`. -/
def mkConcat (r₁ r₂ : TRe) : TRe :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

/-- `native_re_union`. -/
def mkUnion (r₁ r₂ : TRe) : TRe :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if ceq r₁ r₂ then r₁ else .union r₁ r₂

/-- `native_re_inter`. -/
def mkInter (r₁ r₂ : TRe) : TRe :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if ceq r₁ r₂ then r₁ else .inter r₁ r₂

/-- `native_re_comp`. -/
def mkComp : TRe → TRe
  | .comp r => r
  | r => .comp r

/-- `native_re_mult`. -/
def mkStar : TRe → TRe
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

/-- `native_re_deriv` by the character `c`, a valid one (clamped). -/
def deriv (c : Nat) : TRe → TRe
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c == reClamp d then .epsilon else .empty
  | .range lo hi => if reClamp lo ≤ c && c ≤ reClamp hi then .epsilon else .empty
  | .allchar => .epsilon
  | .concat r₁ r₂ =>
    mkUnion (mkConcat (deriv c r₁) r₂) (if nullable r₁ then deriv c r₂ else .empty)
  | .union r₁ r₂ => mkUnion (deriv c r₁) (deriv c r₂)
  | .inter r₁ r₂ => mkInter (deriv c r₁) (deriv c r₂)
  | .star r => mkConcat (deriv c r) (.star r)
  | .comp r => mkComp (deriv c r)

/-- `native_str_in_re`: the string `w` is in `r`. -/
def inRe (w : List Nat) (r : TRe) : Bool :=
  nullable (w.foldl (fun acc c => deriv (reClamp c) acc) r)

/-- `native_str_to_re`. -/
def ofList : List Nat → TRe
  | [] => .epsilon
  | c :: cs => mkConcat (.char c) (ofList cs)

/-- `native_re_range`. -/
def mkRange : List Nat → List Nat → TRe
  | [a], [b] => .range a b
  | _, _ => .empty

/-- `__smtx_re_exp_rec`: `r` repeated `n` times. -/
def exp (r : TRe) : Nat → TRe
  | 0 => .epsilon
  | n + 1 => mkConcat (exp r n) r

/-- `__smtx_re_loop_rec`: the union of `r` repeated `lo` to `hi` times, `n`
of them below `hi`. -/
def loopRec (lo : Int) (r : TRe) : Nat → Int → TRe
  | 0, _ => exp r lo.toNat
  | n + 1, hi => mkUnion (loopRec lo r n (hi + -1)) (exp r hi.toNat)

/-- `__smtx_model_eval_re_loop`. -/
def loop (lo hi : Int) (r : TRe) : TRe :=
  if lo > hi then .empty else loopRec lo r (hi + -lo).toNat hi

end TRe

end Telos.Solver
