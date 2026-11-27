import Telos.Core.AciNorm

/-!
# Length-based splits of string equalities

cvc5's `rewriteViaStrEqLenUnify` (`SPLIT_EQ`, a case of
`rewriteStrEqualityExt`): an equality of two concatenations of strings
`(= (str.++ x₁ … xₙ) (str.++ y₁ … yₘ))` whose prefixes `x₁ … xᵢ` and `y₁ … yⱼ`
have equal lengths is the conjunction of the equality of the prefixes and that
of the suffixes, `(and (= P₀ P₁) (= S₀ S₁))`.

It is a semantic step (`SemProc.strSplit`, `Telos/Core/Semantic.lean`), whose
side condition `ok` asks that the lengths be equal in every model for a reason
read off the components (`lenEq`): the prefixes have the same non-constant
components, up to their order, and constants of the same total length.
`verification/TelosProofs/Core/StrSplit.lean` proves the step an equivalence,
from Logos's semantics of `str.++` (the concatenation of the values' lists).
-/

namespace Telos.StrSplit

/-- The concatenation of the components `cs`: the component itself for one,
their `str.++` otherwise. -/
def cat : List Node → Node
  | [c] => c
  | cs => .app (.kind .STRING_CONCAT) ⟨cs⟩

/-- The length of a string constant. -/
def wordLen : Node → Option Nat
  | .const (.string w) => some w.length
  | _ => none

/-- The components of `cs` that are not constants. -/
def others (cs : List Node) : List Node := cs.filter fun c => (wordLen c).isNone

/-- The total length of the constants of `cs`. -/
def wordsLen (cs : List Node) : Nat := (cs.filterMap wordLen).sum

/-- The components `ps` and `qs` have the same length in every model: the same
non-constant components, up to their order, and constants of the same total
length. -/
def lenEq (ps qs : List Node) : Bool :=
  decide ((others ps).Perm (others qs)) && wordsLen ps == wordsLen qs

/-- `(and (= P₀ P₁) (= S₀ S₁))`, for the prefixes of `i` and `j` components of
`as` and `bs` and the suffixes after them. -/
def target (as bs : List Node) (i j : Nat) : Node :=
  .app (.kind .AND) #[.app (.kind .EQUAL) #[cat (as.take i), cat (bs.take j)],
    .app (.kind .EQUAL) #[cat (as.drop i), cat (bs.drop j)]]

/-- The components of the sides of `n`, an equality of two concatenations. -/
def sides? (n : Node) : Option (List Node × List Node) :=
  match n with
  | .app (.kind .EQUAL) cs =>
    match cs.toList with
    | [.app (.kind .STRING_CONCAT) a, .app (.kind .STRING_CONCAT) b] => some (a.toList, b.toList)
    | _ => none
  | _ => none

/-- The side condition of a split of `n` to `m` at `i` and `j`: `n` is an
equality of two concatenations of strings (`AciConcat.isConcat`), the prefixes
and suffixes are not empty, the prefixes have equal lengths (`lenEq`), and `m`
is the split (`target`). -/
def ok (i j : Nat) (n m : Node) : Bool :=
  match sides? n with
  | some (as, bs) =>
    AciConcat.isConcat ⟨as⟩ && AciConcat.isConcat ⟨bs⟩ &&
      decide (0 < i) && decide (i < as.length) && decide (0 < j) && decide (j < bs.length) &&
      lenEq (as.take i) (bs.take j) && m == target as bs i j
  | none => false

end Telos.StrSplit
