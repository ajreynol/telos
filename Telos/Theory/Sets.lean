import Telos.Theory.Common
import Telos.Rewriter.Rewriter

/-!
# The sets rewriter

A port of cvc5's `TheorySetsRewriter` (`src/theory/sets/theory_sets_rewriter.cpp`)
for the set operators of cvc5's safe mode that CPC has: `set.empty`,
`set.singleton`, `set.union`, `set.inter`, `set.minus`, `set.member`,
`set.subset`, `set.choose`, `set.is_empty`, `set.is_singleton` and
`set.insert`. Safe mode excludes `set.card`, the relations, `set.universe`,
`set.complement` and comprehensions; `set.map`, `set.filter`, `set.fold`,
`set.all` and `set.some` have no CPC counterpart.

Each step is a CPC rule:

* `set.insert` and `set.subset` are eliminated in pre-rewriting
  (`sets-insert-elim`, `sets-subset-elim`);
* `set.member` of the empty set is `false` (`sets-member-emp`), of a singleton an
  equality (`sets-member-singleton`), and of a union, intersection or difference
  a disjunction or conjunction of memberships (`sets-union-member`, …);
* `set.minus`, `set.inter` and `set.union` with an empty side
  (`sets-minus-emp1`, …), of a set with itself (`sets-minus-self`), and of two
  constant sets (`sets-eval-op`, with the result computed here); the arguments
  of `set.inter` and `set.union` are ordered (`sets-inter-comm`,
  `sets-union-comm`);
* `set.choose` of a singleton (`sets-choose-singleton`); `set.is_empty` is an
  equality with the empty set (`sets-is-empty-elim`), and `set.is_singleton` of
  the empty set or of a singleton is `false` or `true`, and otherwise an
  equality (`sets-is-singleton-elim`,
  then `sets-eq-singleton-emp`, or `sets-choose-singleton` and `eq-refl`);
* equalities of sets: `true` for equal sides (`eq-refl`), `false` for distinct
  constants (`distinct_values`, `false_intro`), and otherwise oriented by the
  term order (`eq-symm`).

The rules whose premise is `(= x (as set.empty (Set T)))` are applied when `x`
is the empty set, with the premise proven by `refl`.

A set constant is cvc5's: `(set.union (set.singleton c₁) (… (set.singleton cₙ)))`
with constant elements `c₁ > … > cₙ` (`NormalForm::checkNormalConstant`), or a
singleton of a constant, or the empty set.

Deviations from cvc5:

* `(set.union s s)` and `(set.inter s s)` are left unchanged. cvc5 rewrites them
  to `s` but has no proof rule for that (a `TRUST_THEORY_REWRITE` step;
  reproducers in `test/cvc5-trust/`).
* The membership of a constant in a constant set is computed by the general
  membership rewrites, then evaluating the element equalities, where cvc5
  decides it at once (`checkConstantMembership`). The result is the same.
* `set.is_empty` of a constant goes through its equality with the empty set,
  where cvc5 returns the constant at once; the result is the same.
* cvc5 orders set elements and arguments by node id; telos by its term order
  (`Node.lt`).
-/

open Eo

namespace Telos

namespace SetsRewriter

open Node

/-- The element type of the empty set `n`, if it is one. -/
def emptyElem? : Node → Option TypeNode
  | .const (.emptySet T) => some T
  | _ => none

def isEmptySet (n : Node) : Bool := (emptyElem? n).isSome

/-- The element type of a set term, from its type. -/
def elemType? (n : Node) : Option TypeNode :=
  match n.typeHint with
  | some (.set T) => some T
  | _ => none

mutual

/-- cvc5's `isConst`: constants, and set constants in normal form. -/
partial def isConstNode (n : Node) : Bool :=
  match n with
  | .const _ => true
  | .app (.kind .SET_SINGLETON) #[c] => isConstNode c
  | .app (.kind .SET_UNION) #[_, _] => (normalElems n).isSome
  | _ => false

/-- The elements `c₁ > … > cₙ` of a set constant
`(set.union (set.singleton c₁) (… (set.singleton cₙ)))` (`n ≥ 2`), in that
order (`NormalForm::checkNormalConstant`). -/
partial def normalElems (n : Node) : Option (List Node) :=
  match n with
  | .app (.kind .SET_UNION) #[.app (.kind .SET_SINGLETON) #[c], rest] => do
    if !isConstNode c then none
    let cs ← match rest with
      | .app (.kind .SET_SINGLETON) #[d] => if isConstNode d then some [d] else none
      | _ => normalElems rest
    match cs with
    | d :: _ => if d.lt c then some (c :: cs) else none
    | [] => none
  | _ => none

end

/-- The elements of a set constant (`NormalForm::getElementsFromNormalConstant`). -/
def constElems (n : Node) : Option (List Node) :=
  match n with
  | .const (.emptySet _) => some []
  | .app (.kind .SET_SINGLETON) #[c] => some [c]
  | _ => normalElems n

/-- The set constant with these elements (`NormalForm::elementsToSet`): the
largest element outermost. -/
def elementsToSet (T : TypeNode) (es : List Node) : Node :=
  match (es.eraseDups.mergeSort fun a b => a.lt b) with
  | [] => .const (.emptySet T)
  | e :: es => es.foldl (fun cur x => mkNode .SET_UNION #[mkNode .SET_SINGLETON #[x], cur])
      (mkNode .SET_SINGLETON #[e])

/-- A rule step with the given arguments (terms, so that types can be passed),
after the steps proving its premises, in order. -/
def byRuleArgs (r : CRule) (args : List Term) (premiseSteps : List CCmd) (n : Node) :
    Option (Rw n) :=
  let ruleStep := CCmd.step r (toArgList args) (RuleSpec.premiseIndices premiseSteps.length)
  applyCmds ((premiseSteps ++ [ruleStep]).foldr .cons .nil) n

/-- A rule `r x y (Set T)` whose premise says that the empty set `e` (`x` or
`y`) is `(as set.empty (Set T))`, proven by `refl`. -/
def byEmptyRule (r : CRule) (x y e : Node) (n : Node) : Option (Rw n) := do
  let T ← emptyElem? e
  byRuleArgs r [x.toEo, y.toEo, (TypeNode.set T).toEo] [stepCmd .refl [e]] n

/-- `(= a b)` is `false` for distinct constants `a` and `b`
(`distinct_values`, then `false_intro`). -/
def eqDistinctConsts (a b : Node) (n : Node) : Option (Rw n) :=
  byRuleArgs .false_intro [] [stepCmd .distinct_values [a, b]] n

def respond {n : Node} (st : RewriteStatus) : Option (Rw n) → RewriteResponse n
  | some ⟨m, h⟩ => ⟨st, m, h⟩
  | none => .done n

/-- cvc5's `SETS_EVAL_OP` (`rewriteViaRule`): the union, intersection or
difference of two set constants, certified by `sets-eval-op`. -/
def evalOp (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let as ← constElems a
  let bs ← constElems b
  let T ← elemType? a
  let es := match n.getKind with
    | .SET_UNION => as ++ bs
    | .SET_INTER => as.filter (bs.contains ·)
    | _ => as.filter (!bs.contains ·)
  checkBy .sets_eval_op n (elementsToSet T es)

/-- `set.union`, `set.inter` and `set.minus` (cvc5's `postRewrite`). -/
def rewriteBinary (n : Node) : RewriteResponse n :=
  match n.getKind, n.getChildren with
  | k, #[a, b] =>
    if a == b && k == .SET_MINUS then respond .REWRITE_DONE (byRule "sets-minus-self" n)
    -- `(set.union s s)` and `(set.inter s s)` are `s` in cvc5, by a trusted step
    -- unless `s` is a constant, where the rules below prove it.
    else if a == b && !isConstNode a then .done n
    else if isEmptySet a then
      match k with
      | .SET_MINUS => respond .REWRITE_AGAIN (byEmptyRule .sets_minus_emp1 a b a n)
      | .SET_INTER => respond .REWRITE_AGAIN (byEmptyRule .sets_inter_emp1 a b a n)
      | _ => respond .REWRITE_AGAIN (byEmptyRule .sets_union_emp1 a b a n)
    else if isEmptySet b then
      match k with
      | .SET_MINUS => respond .REWRITE_AGAIN (byEmptyRule .sets_minus_emp2 a b b n)
      | .SET_INTER => respond .REWRITE_AGAIN (byEmptyRule .sets_inter_emp2 a b b n)
      | _ => respond .REWRITE_AGAIN (byEmptyRule .sets_union_emp2 a b b n)
    else if isConstNode a && isConstNode b then respond .REWRITE_DONE (evalOp n)
    else if k != .SET_MINUS && b.lt a then
      respond .REWRITE_DONE (byRule (if k == .SET_INTER then "sets-inter-comm" else "sets-union-comm") n)
    else .done n
  | _, _ => .done n

/-- `set.member` (cvc5's `postRewrite` and `rewriteMembershipBinaryOp`). -/
def rewriteMember (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[x, s] =>
    if isEmptySet s then respond .REWRITE_DONE (byEmptyRule .sets_member_emp x s s n)
    else match s.getKind with
      | .SET_SINGLETON => respond .REWRITE_AGAIN_FULL (byRule "sets-member-singleton" n)
      | .SET_UNION => respond .REWRITE_AGAIN_FULL (byRule "sets-union-member" n)
      | .SET_INTER => respond .REWRITE_AGAIN_FULL (byRule "sets-inter-member" n)
      | .SET_MINUS => respond .REWRITE_AGAIN_FULL (byRule "sets-minus-member" n)
      | _ => .done n
  | _ => .done n

/-- Equalities of sets (cvc5's `preRewrite` and `postRewrite`). -/
def rewriteEqual (pre : Bool) (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[a, b] =>
    if a == b then respond .REWRITE_DONE (byRule "eq-refl" n)
    else if pre then .done n
    else if isConstNode a && isConstNode b then respond .REWRITE_DONE (eqDistinctConsts a b n)
    else if b.lt a then respond .REWRITE_DONE (byRule "eq-symm" n)
    else .done n
  | _ => .done n

/-- `set.is_empty`: an equality with the empty set, and for a constant its value. -/
def rewriteIsEmpty (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[a] =>
    match byRule "sets-is-empty-elim" n with
    | some r =>
      if isConstNode a then
        let r := r.next fun m => match m.getChildren with
          | #[a', e] => if a' == e then byRule "eq-refl" m else eqDistinctConsts a' e m
          | _ => none
        ⟨.REWRITE_DONE, r.1, r.2⟩
      else ⟨.REWRITE_AGAIN, r.1, r.2⟩
    | none => .done n
  | _ => .done n

/-- `set.is_singleton`: `false` for the empty set, `true` for a singleton, and
otherwise `(= A (set.singleton (set.choose A)))`. -/
def rewriteIsSingleton (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[a] =>
    if isEmptySet a then
      respond .REWRITE_DONE <| (byRule "sets-is-singleton-elim" n).bind fun r =>
        -- `(= a (set.singleton (set.choose a)))` is `false` for the empty `a`.
        r.next? fun m => byEmptyRule .sets_eq_singleton_emp a (mkNode .SET_CHOOSE #[a]) a m
    else if a.getKind == .SET_SINGLETON then
      respond .REWRITE_DONE <| (byRule "sets-is-singleton-elim" n).bind fun r =>
        -- `(= {x} {(set.choose {x})})` is `(= {x} {x})`, which is `true`.
        r.next? (fun m => Rw.congrArg m 1 fun s => Rw.congrArg s 0 (byRule "sets-choose-singleton"))
          |>.bind fun r => r.next? (byRule "eq-refl")
    -- `(set.is_singleton A)` is `(= A (set.singleton (set.choose A)))`.
    else respond .REWRITE_AGAIN_FULL (byRule "sets-is-singleton-elim" n)
  | _ => .done n

def postRewrite (n : Node) : RewriteResponse n :=
  if isConstNode n then .done n else
  match n.getKind with
  | .SET_MEMBER => rewriteMember n
  | .SET_SUBSET => respond .REWRITE_AGAIN_FULL (byRule "sets-subset-elim" n)
  | .EQUAL => rewriteEqual false n
  | .SET_MINUS | .SET_INTER | .SET_UNION => rewriteBinary n
  | .SET_CHOOSE =>
    if (n.getChildren[0]?.map (·.getKind)) == some .SET_SINGLETON then
      respond .REWRITE_AGAIN (byRule "sets-choose-singleton" n)
    else .done n
  | .SET_IS_EMPTY => rewriteIsEmpty n
  | .SET_IS_SINGLETON => rewriteIsSingleton n
  | _ => .done n

def preRewrite (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .EQUAL => rewriteEqual true n
  | .SET_INSERT => respond .REWRITE_AGAIN (byRule "sets-insert-elim" n)
  | .SET_SUBSET => respond .REWRITE_AGAIN (byRule "sets-subset-elim" n)
  | _ => .done n

end SetsRewriter

/-- cvc5's `TheorySetsRewriter`. -/
def TheoryRewriter.sets : TheoryRewriter where
  preRewrite := SetsRewriter.preRewrite
  postRewrite := SetsRewriter.postRewrite

end Telos
