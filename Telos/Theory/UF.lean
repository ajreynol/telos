import Telos.Theory.Common
import Telos.Rewriter.Rewriter

/-!
# The UF rewriter

A port of cvc5's `TheoryUfRewriter` (`src/theory/uf/theory_uf_rewriter.cpp`), for
the nodes it owns that telos has: equalities over uninterpreted sorts and
functions (by `theoryOf`), and `distinct`.

* Equalities (`preRewrite`, `postRewrite`): `(= t t)` is `true` (`eq-refl`). The
  post-rewrite orients the equality (`eq-symm`) so that the smaller side comes
  first. cvc5 compares node ids; telos uses its fixed term order (`Node.lt`), as
  the Boolean and arithmetic rewriters do.
* `distinct` (`rewriteDistinct`, in both): `false` when there are more children
  than values of a Boolean or bit-vector type (`distinct-card-conflict`) or when a
  child repeats (`distinct-false`), `true` when all children are distinct
  constants (`distinct-true`), and otherwise, for at most 10 children, the
  conjunction of the pairwise disequalities (`blastDistinct`, `distinct-elim`).
  Each result is computed here and validated by the CPC rule, which takes the
  equation as its argument (`checkBy`).

Not ported:
* "uninterpreted constants are all distinct": telos has no uninterpreted
  constants.
* lambdas, `HO_APPLY`, beta reduction, and the `ubv_to_int`/`int_to_bv`
  conversions: telos has none of these kinds yet.

Deviation: the children of a `distinct` with more than 10 children are not
rewritten, since its shape has no congruence proof yet
(`AppShape.isChildCongruent`). Smaller ones are expanded before their children
are rewritten, as in cvc5.
-/

namespace Telos

namespace UfRewriter

open Node

def tt : Node := .const (.boolean true)
def ff : Node := .const (.boolean false)

/-- The disequalities `(not (= xᵢ xⱼ))` for `i < j`, in cvc5's order. -/
def pairwiseDiseqs : List Node → List Node
  | [] => []
  | x :: xs => xs.map (fun y => notNode (eqNode x y)) ++ pairwiseDiseqs xs

/-- cvc5's `blastDistinct`: `(distinct x₁ … xₙ)` as a conjunction of
disequalities, or the disequality itself for two children. -/
def blastDistinct (cs : Array Node) : Node :=
  match pairwiseDiseqs cs.toList with
  | [d] => d
  | ds => mkNode .AND ds.toArray

/-- Whether the number of values of type `T` is less than `k` (cvc5's
`isCardinalityLessThan`, for the types `DISTINCT_CARD_CONFLICT` handles). -/
def cardLessThan (T : TypeNode) (k : Nat) : Bool :=
  match T with
  | .boolean => 2 < k
  | .bitVector w => w ≥ 0 && 2 ^ w.toNat < k
  | _ => false

/-- Whether some child occurs twice. -/
def hasDuplicate : List Node → Bool
  | [] => false
  | x :: xs => xs.contains x || hasDuplicate xs

/-- cvc5's `TheoryUfRewriter::rewriteDistinct`. -/
def rewriteDistinct (n : Node) (cs : Array Node) : Option (Rw n) :=
  if ((cs[0]? >>= Node.typeHint).map (cardLessThan · cs.size)).getD false then checkBy .distinct_card_conflict n ff
  else if hasDuplicate cs.toList then checkBy .distinct_false n ff
  else if cs.all (·.isConst) then checkBy .distinct_true n tt
  else if cs.size ≤ 10 then checkBy .distinct_elim n (blastDistinct cs)
  else none

/-- The rewrites `preRewrite` and `postRewrite` share. -/
def rewriteCommon (n : Node) : Option (Rw n) :=
  match n.getKind, n.getChildren with
  | .EQUAL, #[a, b] => if a == b then byRule "eq-refl" n else none
  | .DISTINCT, cs => rewriteDistinct n cs
  | _, _ => none

/-- cvc5's `rewriteIntToBV`, for a constant argument: its value. -/
def rewriteIntToBV (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[c] => if c.isConst then byEvaluate n else none
  | _ => none

/-- cvc5's `TheoryUfRewriter::preRewrite`. -/
def preRewrite (n : Node) : RewriteResponse n :=
  match rewriteCommon n with
  | some ⟨m, h⟩ => ⟨.REWRITE_DONE, m, h⟩
  | none => .done n

/-- cvc5's `TheoryUfRewriter::postRewrite`: also orients equalities. -/
def postRewrite (n : Node) : RewriteResponse n :=
  let r := (rewriteCommon n).orElse fun _ =>
    match n.getKind, n.getChildren with
    | .EQUAL, #[a, b] => if b.lt a then byRule "eq-symm" n else none
    | _, _ => none
  match r with
  | some ⟨m, h⟩ => ⟨.REWRITE_DONE, m, h⟩
  | none =>
    match n.getKind with
    | .INT_TO_BITVECTOR =>
      match rewriteIntToBV n with
      | some ⟨m, h⟩ => ⟨.REWRITE_AGAIN_FULL, m, h⟩
      | none => .done n
    | _ => .done n

end UfRewriter

/-- cvc5's `TheoryUfRewriter`. -/
def TheoryRewriter.uf : TheoryRewriter where
  preRewrite := UfRewriter.preRewrite
  postRewrite := UfRewriter.postRewrite

end Telos
