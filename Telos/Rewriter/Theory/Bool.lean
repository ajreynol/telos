import Telos.Rewriter.Theory.Common
import Telos.Rewriter.Rewriter

/-!
# The Boolean rewriter

A port of cvc5's `TheoryBoolRewriter::preRewrite` (`src/theory/booleans/
theory_bool_rewriter.cpp`); `postRewrite` is the same function, as in cvc5. The
case analysis follows the C++ line by line. Each result is reached by CPC steps:
RARE rules where one applies, `aci_norm` and `absorb` for `flattenNode`, and
`evaluate` for constants.

Not ported: the proof rewrite rules cvc5 registers (`MACRO_BOOL_NNF_NORM`,
`MACRO_BOOL_BV_INVERT_SOLVE`), which the default rewriter does not call.
-/

namespace Telos

namespace BoolRewriter

open Node

/-- The result of a case: a status and a certified rewrite. -/
abbrev Result (n : Node) := Option (RewriteStatus × Rw n)

def again {n : Node} (r : Option (Rw n)) : Result n := r.map (.REWRITE_AGAIN, ·)
def done {n : Node} (r : Option (Rw n)) : Result n := r.map (.REWRITE_DONE, ·)

/-- Steps that must apply in sequence. -/
def steps {n : Node} (names : List String) : Option (Rw n) :=
  names.foldlM (fun r name => r.next? (byRule name)) (Rw.id n)

/-- cvc5's `makeNegation`, applied to the result of a rewrite to `(not t)`:
remove double negations, and negate constants. -/
partial def negNorm (m : Node) : Rw m :=
  match m.getKind, m.getChildren with
  | .NOT, #[c] =>
    if c.getKind == .NOT then
      match byRule "bool-double-not-elim" m with
      | some r => r.next fun k => some (negNorm k)
      | none => Rw.id m
    else if c == mkTrue || c == mkFalse then (byEvaluate m).getD (Rw.id m)
    else Rw.id m
  | _, _ => Rw.id m

/-- Rewrite to `(not t)` by `r`, then apply `makeNegation`. -/
def negated {n : Node} (r : Option (Rw n)) : Option (Rw n) :=
  r.map (·.next fun k => some (negNorm k))

/-- cvc5's `equalityParity a b`: 1 if `a = b`, 2 if `a = (not b)`, 3 if
`b = (not a)`, and 0 otherwise. -/
def equalityParity (a b : Node) : Nat :=
  if a == b then 1
  else match a, b with
    | .app (.kind .NOT) #[a'], _ => if a' == b then 2 else parity3
    | _, _ => parity3
where
  parity3 := match b with
    | .app (.kind .NOT) #[b'] => if b' == a then 3 else 0
    | _ => 0

/-- cvc5's `flattenNode`, as a status and result node. The result is certified
separately. -/
def flattenResult (k : Kind) (n : Node) (trivial skip : Node) : RewriteStatus × Node := Id.run do
  let mut visited : List Node := [skip]
  let mut toProcess : Array Node := #[n]
  let mut childList : Array Node := #[]
  let mut i := 0
  while h : i < toProcess.size do
    let current := toProcess[i]
    for child in current.getChildren do
      if visited.contains child then continue
      if child == trivial then return (.REWRITE_DONE, trivial)
      visited := child :: visited
      if child.getKind == k then toProcess := toProcess.push child
      else childList := childList.push child
    i := i + 1
  if childList.size == 0 then return (.REWRITE_DONE, skip)
  if h : childList.size = 1 then return (.REWRITE_AGAIN, childList[0])
  return (.REWRITE_DONE, mkNode k childList)

/-- `flattenNode`, certified: by `absorb` when the result is the zero element,
and by `aci_norm` otherwise. -/
def flatten (k : Kind) (n trivial skip : Node) : Result n :=
  let (st, m) := flattenResult k n trivial skip
  let r := if m == trivial then checkBy .absorb n m else checkBy .aci_norm n m
  r.map (st, ·)

/-- The `OR` and `AND` cases. `zero` absorbs (true for `OR`), `unit` is the
neutral element. -/
def nary (k : Kind) (n zero unit : Node) (cs : Array Node) : Result n :=
  if cs.any (· == zero) then done (checkBy .absorb n zero)
  else if cs.any (fun c => c == unit || c.getKind == k) then flatten k n zero unit
  -- x v ... v x --> x
  else if cs.all (· == cs[0]!) then again (checkBy .aci_norm n cs[0]!)
  else none

/-- Flip child `i` of `n`, an equality, by `eq-symm`. -/
def flipChild (n : Node) (i : Nat) : Option (Rw n) :=
  Rw.congrArg n i (byRule "eq-symm")

/-- Apply `f` to `r` only when `b`. -/
def Rw.nextIf {n : Node} (b : Bool) (r : Rw n) (f : (m : Node) → Option (Rw m)) : Option (Rw n) :=
  if b then r.next? f else some r

/-- cvc5's `rewriteViaEqConstEq`: `(= (= t k) (= t z))`, for constants `k` and `z`
and with either equality in either orientation, is `true` when `k = z`, and
otherwise `(and (not (= t k)) (not (= t z)))` (both equalities keeping their
orientation). Certified by flipping the equalities into the form of `eq-refl` or
`eq-cond-deq`, and back. -/
def eqConstEq (n : Node) : Result n :=
  match n.getKind, n.getChildren with
  | .EQUAL, #[.app (.kind .EQUAL) #[a0, b0], .app (.kind .EQUAL) #[a1, b1]] =>
    -- c := n[0][0] and t := n[0][1] if n[0][0] is a constant, and the reverse
    -- if only n[0][1] is
    let side0 : Option (Node × Node × Bool) :=
      if a0.isConst then some (b0, a0, true) else if b0.isConst then some (a0, b0, false) else none
    match side0 with
    | none => none
    | some (t, k, flip0) =>
      let side1 : Option (Node × Bool) :=
        if a1 == t && b1.isConst then some (b1, false)
        else if b1 == t && a1.isConst then some (a1, true) else none
      match side1 with
      | none => none
      | some (z, flip1) =>
        -- (= (= t k) (= t z))
        let normalized : Option (Rw n) := do
          let r ← Rw.nextIf flip0 (Rw.id n) (flipChild · 0)
          Rw.nextIf flip1 r (flipChild · 1)
        if z == k then done (normalized >>= fun r => Rw.next? r (byRule "eq-refl"))
        else
          -- (and (not (= t k)) (not (= t z))), then restore the orientations
          let unflip (i : Nat) (m : Node) : Option (Rw m) :=
            Rw.congrArg m i fun ni => Rw.congrArg ni 0 (byRule "eq-symm")
          again do
            let r ← normalized
            -- The premise `(= (= k z) false)` by `evaluate`, or for datatype
            -- values, which `evaluate` does not decide, by `dt-cons-eq-clash`.
            let clash (m : Node) : Option (Rw m) :=
              byRuleWithPremises .eq_cond_deq [t, k, z]
                [stepCmd .dt_cons_eq_clash [eqNode (eqNode k z) mkFalse]] m
            let r ← Rw.next? r fun m => (byRule "eq-cond-deq" m).orElse fun _ => clash m
            let r ← Rw.nextIf flip0 r (unflip 0)
            Rw.nextIf flip1 r (unflip 1)
  | _, _ => none

def tt : Node := mkTrue
def ff : Node := mkFalse

/-- cvc5's `TheoryBoolRewriter::preRewrite`, without its final default. -/
def rewriteCase (n : Node) : Result n :=
  match n.getKind, n.getChildren with
  | .NOT, #[c] =>
    if c == tt || c == ff then done (byEvaluate n)
    else if c.getKind == .NOT then again (byRule "bool-double-not-elim" n)
    else none
  | .OR, cs => nary .OR n tt ff cs
  | .AND, cs => nary .AND n ff tt cs
  | .IMPLIES, #[a, b] =>
    if a == ff then done (byRule "bool-impl-false2" n)
    else if b == tt then done (byRule "bool-impl-true1" n)
    else if a == tt && b == ff then done (byEvaluate n)
    else if a == tt then again (byRule "bool-impl-true2" n)
    else if b == ff then again (negated (byRule "bool-impl-false1" n))
    else none
  | .EQUAL, #[a, b] =>
    if a == tt then again (steps ["eq-symm", "bool-eq-true"])
    else if b == tt then again (byRule "bool-eq-true" n)
    else if a == ff then again (negated (steps ["eq-symm", "bool-eq-false"]))
    else if b == ff then again (negated (byRule "bool-eq-false" n))
    else if a == b then done (byRule "eq-refl" n)
    else if a == notNode b then done (steps ["eq-symm", "bool-eq-nrefl"])
    else if b == notNode a then done (byRule "bool-eq-nrefl" n)
    else match eqConstEq n with
      | some r => some r
      | none =>
        -- sort
        if b.lt a then again (byRule "eq-symm" n) else none
  | .XOR, #[a, b] =>
    if a == tt then again (negated (steps ["bool-xor-comm", "bool-xor-true"]))
    else if b == tt then again (negated (byRule "bool-xor-true" n))
    else if a == ff then again (steps ["bool-xor-comm", "bool-xor-false"])
    else if b == ff then again (byRule "bool-xor-false" n)
    else if a == b then done (byRule "bool-xor-refl" n)
    else if a == notNode b then done (steps ["bool-xor-comm", "bool-xor-nrefl"])
    else if b == notNode a then done (byRule "bool-xor-nrefl" n)
    else none
  | .ITE, #[c, x, y] => iteCase n c x y
  | _, _ => none
where
  iteCase (n c x y : Node) : Result n :=
    if c.isConst then
      if c == tt then again (byRule "ite-true-cond" n)
      else again (byRule "ite-false-cond" n)
    else if x == tt && y == ff then
      -- (ite c true false) --> c, as (or c false) --> c
      again ((byRule "ite-then-true" n).bind (·.next? fun m => checkBy .aci_norm m c))
    else if x == ff && y == tt then
      -- (ite c false true) --> (not c), as (and (not c) true) --> (not c)
      again (negated ((byRule "ite-then-false" n).bind
        (·.next? fun m => checkBy .aci_norm m (notNode c))))
    else if c.getKind == .NOT then
      -- ite(not(c), x, y) ---> ite(c, y, x)
      again (byRule "ite-not-cond" n)
    else
      let p := equalityParity x y
      if p != 0 then
        again <|
          if p == 1 then byRule "ite-eq-branch" n
          -- (ite c (not y) y): the premise (= (not y) (not y)) of ite-neg-branch
          else if p == 2 then byRuleWithPremises .ite_neg_branch [c, x, y]
            [stepCmd .refl [notNode y]] n
          -- (ite c x (not x)): the premise (= (not (not x)) x) of ite-neg-branch
          else byRuleWithPremises .ite_neg_branch [c, x, y]
            [stepCmd .bool_double_not_elim [x]] n
      else
      let p := equalityParity c x
      if !x.isConst && p != 0 then
        again (byRule (if p == 1 then "ite-then-lookahead-self"
          else "ite-then-lookahead-not-self") n)
      else
      let p := equalityParity c y
      if !y.isConst && p != 0 then
        again (byRule (if p == 1 then "ite-else-lookahead-self"
          else "ite-else-lookahead-not-self") n)
      else
      let p := iteCondParity c x
      if p != 0 then
        again (byRule (if p == 1 then "ite-then-lookahead" else "ite-then-neg-lookahead") n)
      else
      let p := iteCondParity c y
      if p != 0 then
        again (byRule (if p == 1 then "ite-else-lookahead" else "ite-else-neg-lookahead") n)
      else constBranch n c x y
  /-- `equalityParity c c'` if `t` is `(ite c' _ _)`, and 0 otherwise. -/
  iteCondParity (c t : Node) : Nat :=
    match t with
    | .app (.kind .ITE) #[c', _, _] => equalityParity c c'
    | _ => 0
  /-- ITEs with a constant Boolean branch. -/
  constBranch (n _c x y : Node) : Result n :=
    if x == tt then again (byRule "ite-then-true" n)
    else if x == ff then again (byRule "ite-then-false" n)
    else if y == tt then again (byRule "ite-else-true" n)
    else if y == ff then again (byRule "ite-else-false" n)
    else none

/-- cvc5's `TheoryBoolRewriter::preRewrite`. -/
def preRewrite (n : Node) : RewriteResponse n :=
  match rewriteCase n with
  | some (st, ⟨m, h⟩) => ⟨st, m, h⟩
  | none => .done n

end BoolRewriter

/-- cvc5's `TheoryBoolRewriter`. Its post-rewrite is its pre-rewrite. -/
def TheoryRewriter.bool : TheoryRewriter where
  preRewrite := BoolRewriter.preRewrite
  postRewrite := BoolRewriter.preRewrite

end Telos
