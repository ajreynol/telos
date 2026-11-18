import Telos.Rewriter.Theory.BV

/-!
# Bit-vector theory preprocessing

cvc5's `TheoryBV::ppRewrite` (`src/theory/bv/theory_bv.cpp`), with the default
bit-blasting solver (whose own `ppRewrite` does nothing):

* `UltAddOne`: `(bvult x (bvadd y 1))` is `(and (not (= y ones)) (not (bvult y x)))`
  (`bv-ult-add-one`), for an addition of exactly one non-constant and the
  constant `1`;
* `eliminateOverflows`: the overflow predicates as bit-vector formulas, which
  the rewriter does only for constant arguments (`BvRewriter.eliminateOverflows`).
-/

namespace Telos.Preprocess

open Node

/-- `RewriteRule<UltAddOne>::applies`. -/
def ultAddOneApplies (n : Node) : Bool :=
  match n.getKind, n.getChildren with
  | .BITVECTOR_ULT, #[_, .app (.kind .BITVECTOR_ADD) #[a, b]] =>
    let one (c : Node) : Bool := match c with
      | .const (.bitVector _ 1) => true
      | _ => false
    (a.isConst != b.isConst) && (one a || one b)
  | _, _ => false

/-- `TheoryBV::ppRewrite`. -/
def bvPpRewrite (n : Node) : Option (Rw n) :=
  let r : Rw n := if ultAddOneApplies n then (byRule "bv-ult-add-one" n).getD (Rw.id n)
    else Rw.id n
  let r := r.next BvRewriter.eliminateOverflows
  if r.1 == n then none else some r

end Telos.Preprocess
