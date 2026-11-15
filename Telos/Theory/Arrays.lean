import Telos.Theory.Common
import Telos.Rewriter.Rewriter
import Telos.Proof.Emit

/-!
# The arrays rewriter

A port of cvc5's `TheoryArraysRewriter` (`src/theory/arrays/theory_arrays_rewriter.cpp`)
for `select`, `store` and equalities of arrays. Each step is one of CPC's RARE
rules for arrays:

* `select` over `store` (`preRewrite` and `postRewrite`): the stored value when
  the indices are equal (`array-read-over-write`), else the `select` from the
  array below when they are distinct constants (`array-read-over-write2`, whose
  premise `(= (= i j) false)` is proven by `evaluate`), repeatedly;
* `store` of the array's own `select` is the array (`array-store-self`), and a
  `store` over a `store` to the same index replaces it (`array-store-overwrite`);
* in post-rewriting, a `store` over a `store` to a distinct constant index that
  comes later in the term order is swapped below it (`array-store-swap`), so
  that the indices of a chain of `store`s are sorted. cvc5 moves the `store` down
  the chain at once; telos swaps once and rewrites again (`REWRITE_AGAIN_FULL`),
  which reaches the same normal form;
* equalities of arrays: `true` for equal sides (`eq-refl`), and in
  post-rewriting oriented by the term order (`eq-symm`).

Deviations from cvc5:

* cvc5 decides whether two indices are equal by rewriting their equality
  (`mkEqNode`), so that, for example, `x` and `(+ x 1)` are distinct indices.
  telos does the same with the rewriter it is given (`eqRw`), and proves the
  premise `(= (= i j) false)` of `array-read-over-write2` and `array-store-swap`
  by the CPC proof of that rewrite (`Proof.emitProof`). An index equality that
  rewrites to `true` without the indices being equal is left as it is.
* Constant arrays (`store_all`, `((as const (Array Int Int)) 0)`) have no CPC
  counterpart in Logos, so `select` over them and the normalization of constant
  arrays are not ported.
* cvc5 orders indices and the sides of equalities by node id; telos by its term
  order (`Node.lt`).
-/

namespace Telos

namespace ArraysRewriter

open Node

/-- What is known about two indices. -/
inductive IndexRel where
  | equal
  /-- Distinct constants: the premise `(= (= i j) false)` is proven by
  `evaluate`. -/
  | distinctConsts
  /-- Distinct, by these commands proving `(= (= i j) false)`. -/
  | distinctBy (cmds : List Eo.CCmd)
  | unknown

/-- cvc5's test of two indices, with `mkEqNode`: their equality rewritten by
`eqRw`. -/
def indexRel (eqRw : (m : Node) → Rw m) (i j : Node) : IndexRel :=
  if i == j then .equal
  else if i.isConst && j.isConst then .distinctConsts
  else
    let r := eqRw (eqNode i j)
    if r.1 == .const (.boolean false) then
      match Proof.cmdsOf r with
      | some cmds => .distinctBy cmds
      | none => .unknown
    else .unknown

/-- Apply `rule` with `args` to `n`, its premise `(= (= i j) false)` proven by
`premise`. -/
def byRuleAfter (rule : Eo.CRule) (args : List Node) (premise : List Eo.CCmd) (n : Node) :
    Option (Rw n) :=
  applyCmds ((premise ++ [Eo.CCmd.step rule (toArgList (args.map Node.toEo)) (.cons 0 .nil)]).foldr .cons .nil) n

/-- `select` over `store`s: the stored value, or the `select` from the array
below the `store`s to distinct indices. `changed` tells whether a step was
taken. -/
partial def selectOverStore (eqRw : (m : Node) → Rw m) (n : Node) : Rw n :=
  let cs := n.getChildren
  if n.getKind != .SELECT || cs.size != 2 then Rw.id n else
  match cs[0]! with
  | .app (.kind .STORE) #[t, i, e] =>
    let j := cs[1]!
    let step : Option (Rw n) := match indexRel eqRw i j with
      | .equal => none
      | .distinctConsts => byRule "array-read-over-write2" n
      | .distinctBy cmds => byRuleAfter .array_read_over_write2 [t, i, j, e] cmds n
      | .unknown => none
    if i == j then (byRule "array-read-over-write" n).getD (Rw.id n)
    else match step with
      | some r => r.next fun m => some (selectOverStore eqRw m)
      | none => Rw.id n
  | _ => Rw.id n

/-- The rewrites `preRewrite` and `postRewrite` share for `select`: the value of
a `select` over a `store` to the same index is `REWRITE_AGAIN` in
pre-rewriting, and `REWRITE_DONE` otherwise. -/
def rewriteSelect (eqRw : (m : Node) → Rw m) (pre : Bool) (n : Node) : RewriteResponse n :=
  -- cvc5's pre-rewrite does not use `mkEqNode`.
  let r := selectOverStore (if pre then fun m => Rw.id m else eqRw) n
  if r.1 == n then .done n
  else if pre && r.1.getKind != .SELECT then ⟨.REWRITE_AGAIN, r.1, r.2⟩
  else ⟨.REWRITE_DONE, r.1, r.2⟩

/-- cvc5's `postRewrite` and `preRewrite` for `store`. -/
def rewriteStore (eqRw : (m : Node) → Rw m) (pre : Bool) (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[a, i, v] =>
    -- store(a, i, select(a, i)) = a
    let selfStore := match v.getKind, v.getChildren with
      | .SELECT, #[a', i'] => a' == a && i' == i
      | _, _ => false
    if selfStore then
      match byRule "array-store-self" n with
      | some ⟨m, h⟩ => ⟨if pre then .REWRITE_AGAIN else .REWRITE_DONE, m, h⟩
      | none => .done n
    else
      match a.getKind, a.getChildren with
      | .STORE, #[t, j, w] =>
        -- cvc5's pre-rewrite does not use `mkEqNode`.
        let rel := indexRel (if pre then fun m => Rw.id m else eqRw) j i
        let swap := fun (r : Option (Rw n)) => match r with
          | some ⟨m, h⟩ => (⟨.REWRITE_AGAIN_FULL, m, h⟩ : RewriteResponse n)
          | none => .done n
        match rel with
        | .equal =>
          -- store(store(a, i, v), i, w) = store(a, i, w)
          match byRule "array-store-overwrite" n with
          | some ⟨m, h⟩ => ⟨.REWRITE_AGAIN, m, h⟩
          | none => .done n
        -- store(store(a, j, w), i, v) = store(store(a, i, v), j, w) when i
        -- comes before j
        | .distinctConsts => if !pre && i.lt j then swap (byRule "array-store-swap" n) else .done n
        | .distinctBy cmds =>
          if !pre && i.lt j then swap (byRuleAfter .array_store_swap [t, j, i, w, v] cmds n)
          else .done n
        | .unknown => .done n
      | _, _ => .done n
  | _ => .done n

/-- cvc5's rewrites of equalities of arrays. -/
def rewriteEqual (pre : Bool) (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[a, b] =>
    if a == b then
      match byRule "eq-refl" n with
      | some ⟨m, h⟩ => ⟨.REWRITE_DONE, m, h⟩
      | none => .done n
    else if !pre && b.lt a then
      match byRule "eq-symm" n with
      | some ⟨m, h⟩ => ⟨.REWRITE_DONE, m, h⟩
      | none => .done n
    else .done n
  | _ => .done n

/-- The rewrite of `n`, with `eqRw` the rewriter for the equalities of
indices (cvc5's `mkEqNode`). -/
def rewrite (eqRw : (m : Node) → Rw m) (pre : Bool) (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .SELECT => rewriteSelect eqRw pre n
  | .STORE => rewriteStore eqRw pre n
  | .EQUAL => rewriteEqual pre n
  | _ => .done n

end ArraysRewriter

/-- cvc5's `TheoryArraysRewriter`, with `eqRw` the rewriter for equalities of
indices. -/
def TheoryRewriter.arrays (eqRw : (m : Node) → Rw m) : TheoryRewriter where
  preRewrite := ArraysRewriter.rewrite eqRw true
  postRewrite := ArraysRewriter.rewrite eqRw false

end Telos
