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

/-! ### Searching for a match -/

/-- `native_re_prefix_match_len?`: the length of the shortest prefix of `w` in
`r`, plus `n`. -/
def prefixLen (r : TRe) : List Nat → Nat → Option Nat
  | [], n => if nullable r then some n else none
  | c :: cs, n => if nullable r then some n else prefixLen (deriv (reClamp c) r) cs (n + 1)

/-- `native_re_positive_prefix_match_len?`. -/
def posPrefixLen (r : TRe) : List Nat → Option Nat
  | [] => none
  | c :: cs =>
    match prefixLen (deriv (reClamp c) r) cs 0 with
    | some n => some (n + 1)
    | none => none

/-- `native_re_find_idx_from`, on the rest `w` of the string at `i`: the
position and the length of the first match. -/
def findIdx (r : TRe) : List Nat → Nat → Option (Nat × Nat)
  | [], i =>
    match prefixLen r [] 0 with
    | some n => some (i, n)
    | none => none
  | c :: cs, i =>
    match prefixLen r (c :: cs) 0 with
    | some n => some (i, n)
    | none => findIdx r cs (i + 1)

/-- `native_str_indexof_re`. -/
def indexOf (w : List Nat) (r : TRe) (i : Int) : Int :=
  if i < 0 then -1
  else if i.toNat ≤ w.length then
    match findIdx r (w.drop i.toNat) i.toNat with
    | some (idx, _) => Int.ofNat idx
    | none => -1
  else -1

/-- `native_str_replace_re`. -/
def replace (w : List Nat) (r : TRe) (u : List Nat) : List Nat :=
  match findIdx r w 0 with
  | some (idx, len) => w.take idx ++ u ++ w.drop (idx + len)
  | none => w

/-- `impl_native_re_replace_all_nonempty_list_aux`. -/
def replaceAllRec (r : TRe) (u : List Nat) : Nat → List Nat → List Nat
  | 0, xs => xs
  | fuel + 1, xs =>
    match posPrefixLen r xs with
    | some (n + 1) => u ++ replaceAllRec r u fuel (xs.drop (n + 1))
    | _ =>
      match xs with
      | [] => []
      | c :: cs => c :: replaceAllRec r u fuel cs

/-- `native_str_replace_re_all`. -/
def replaceAll (w : List Nat) (r : TRe) (u : List Nat) : List Nat := replaceAllRec r u (w.length + 1) w

end TRe

end Telos.Solver
