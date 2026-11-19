import Std.Data.HashSet
import Telos.Rewriter.Theory.BVNorm
import Telos.Preprocess.SkolemSteps

/-!
# Bit-vector static rewriting

cvc5's `TheoryBV::ppStaticRewrite` (`src/theory/bv/theory_bv.cpp`): an equality
is rewritten by `RewriteRule<SolveEq>`
(`theory_bv_rewrite_rules_normalization.h`), which collects the terms of both
sides with their coefficients, cancels the terms that occur on both sides and
moves the constants to the right. `BitwiseEq` and the `rwExtendEq` rules are off
by default (expert options), and are not ported.

The result `(= a b)` is certified by `bv_poly_norm_eq`: `a - b` is `l - r` or
its negation, as polynomials modulo `2^w` (the premise, by `bv_poly_norm`). A
result `true` or `false` is the equality of two constants, then `evaluate`.

cvc5 orders the coefficient maps and the two sides of the result by node id;
telos uses its term order (`Node.lt`), as `BvNorm` does. The case
`(= x (bvnot x))`, `false`, is `bv-not-neq` (after `eq-symm` for
`(= (bvnot x) x)`).
-/

namespace Telos.Preprocess

open Node BvNorm

/-- Whether `v` occurs in `n`, visiting each shared subterm once. -/
partial def occursDag (v n : Node) : Bool :=
  (go n |>.run {}).1
where
  go (m : Node) : StateM (Std.HashSet Node) Bool := do
    if m == v then return true
    if (← get).contains m then return false
    modify (·.insert m)
    match m with
    | .skolem _ cs => cs.anyM go
    | _ => m.getChildren.anyM go

/-- The coefficient map and constant of one side (`updateCoefMap` over the
children of a `bvadd`, or the side itself), its terms in the term order and
its coefficients modulo `2^w`. -/
def solveEqSide (w : Nat) (t : Node) : List (Node × Nat) × Nat :=
  let (m, c) := if t.getKind == .BITVECTOR_ADD then
      t.getChildren.foldl (fun (m, s) c => updateCoefMap m s c) (([] : CoefMap), (0 : Int))
    else updateCoefMap [] 0 t
  let md : Int := (2 ^ w : Nat)
  ((m.mergeSort fun a b => !b.1.lt a.1).map fun (t, k) => (t, (k % md).toNat), (c % md).toNat)

/-- The merge of the two coefficient maps: the children of each side, and
whether a term occurs on both. -/
def solveEqMerge (w : Nat) :
    List (Node × Nat) → List (Node × Nat) → List Node × List Node × Bool
  | [], [] => ([], [], false)
  | (t, c) :: ls, [] =>
    let (l, r, ch) := solveEqMerge w ls []; (addToChildren w t c ++ l, r, ch)
  | [], (t, c) :: rs =>
    let (l, r, ch) := solveEqMerge w [] rs; (l, addToChildren w t c ++ r, ch)
  | (tl, cl) :: ls, (tr, cr) :: rs =>
    if tl == tr then
      let (l, r, _) := solveEqMerge w ls rs
      if cl > cr then (addToChildren w tl (cl - cr) ++ l, r, true)
      else if cr > cl then (l, addToChildren w tr (cr - cl) ++ r, true)
      else (l, r, true)
    else if tl.lt tr then
      let (l, r, ch) := solveEqMerge w ls ((tr, cr) :: rs); (addToChildren w tl cl ++ l, r, ch)
    else
      let (l, r, ch) := solveEqMerge w ((tl, cl) :: ls) rs; (l, addToChildren w tr cr ++ r, ch)
termination_by ls rs => ls.length + rs.length

/-- cvc5's `RewriteRule<SolveEq>`, `applies` then `apply`: the result, and a
pair `(a, b)` with `a - b = ±(l - r)` that certifies it (the result itself, or
for `true` and `false` two constants). -/
def solveEq (n : Node) : Option (Node × Node × Node) := do
  let #[left, right] := n.getChildren | none
  if n.getKind != .EQUAL then none
  if left.isVar && !occursDag left right then none
  if right.isVar && !occursDag right left then none
  let w ← width? left
  let zero := mkBv w 0
  if (left.getKind == .BITVECTOR_NOT && left.getChildren[0]? == some right) ||
     (right.getKind == .BITVECTOR_NOT && right.getChildren[0]? == some left) then
    return (mkFalse, zero, zero)
  let md := 2 ^ w
  let (lm, lc) := solveEqSide w left
  let (rm, rc) := solveEqSide w right
  let (cl, cr, changed) := solveEqMerge w lm rm
  let mut childrenLeft := cl
  let mut childrenRight := cr
  let mut changed := changed
  let mut leftConst := lc
  let mut rightConst := rc
  if rightConst != 0 then
    changed := changed || leftConst != 0
    rightConst := (rightConst + md - leftConst) % md
    leftConst := 0
    if rightConst != 0 then childrenRight := childrenRight ++ [mkBv w rightConst]
  else if leftConst != 0 then
    childrenLeft := childrenLeft ++ [mkBv w leftConst]
  if childrenRight.isEmpty && leftConst != 0 then
    -- c = 0 is false
    if childrenLeft.length == 1 then return (mkFalse, mkBv w leftConst, zero)
    childrenRight := [mkBv w ((md - leftConst) % md)]
    childrenLeft := childrenLeft.dropLast
    changed := true
  let mut newLeft := zero
  if childrenLeft.isEmpty then
    if rightConst != 0 then
      -- 0 = c is false
      if childrenRight.length == 1 then return (mkFalse, zero, mkBv w rightConst)
      newLeft := mkBv w ((md - rightConst) % md)
      childrenRight := childrenRight.dropLast
      changed := true
  else newLeft := naryNode .BITVECTOR_ADD childrenLeft
  let newRight := if childrenRight.isEmpty then zero else naryNode .BITVECTOR_ADD childrenRight
  if !changed then none
  if newLeft == newRight then return (mkTrue, zero, zero)
  let res := if newLeft.lt newRight then eqNode newRight newLeft else eqNode newLeft newRight
  let #[a, b] := res.getChildren | none
  return (res, a, b)

/-- `(= l r)` to `(= a b)` by `bv_poly_norm_eq`, with the premise
`(= (bvmul 1 (bvsub l r)) (bvmul cy (bvsub a b)))` by `bv_poly_norm`, for
`cy` `1` or `-1`. -/
def bvPolyNormEq (n : Node) (w : Nat) (a b : Node) : Option (Rw n) := do
  let #[l, r] := n.getChildren | none
  let target := eqNode a b
  let try1 (cy : Nat) : Option (Rw n) :=
    let prem := eqNode (mkNode .BITVECTOR_MULT #[mkBv w 1, mkNode .BITVECTOR_SUB #[l, r]])
      (mkNode .BITVECTOR_MULT #[mkBv w cy, mkNode .BITVECTOR_SUB #[a, b]])
    applyCmds (cmdList [stepWith .bv_poly_norm [prem.toEo],
      .step .bv_poly_norm_eq (.cons (eqFormula n target) .nil) prevPremise]) n
  (try1 1).orElse fun _ => try1 (2 ^ w - 1)

/-- `TheoryBV::ppStaticRewrite`, certified. -/
def bvStaticRewrite (n : Node) : Option (Rw n) := do
  let (res, a, b) ← solveEq n
  if let #[_, .app (.kind .BITVECTOR_NOT) _] := n.getChildren then
    if res == mkFalse && a == b then return ← byRule "bv-not-neq" n
  if let #[.app (.kind .BITVECTOR_NOT) _, _] := n.getChildren then
    if res == mkFalse && a == b then
      return ← (byRule "eq-symm" n).bind fun r => r.next? (byRule "bv-not-neq")
  let w ← width? a
  let r ← bvPolyNormEq n w a b
  if r.1 == res then return r
  r.next? fun m => (byEvaluate m).filter (·.1 == res)

end Telos.Preprocess
