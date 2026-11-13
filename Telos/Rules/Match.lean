import Telos.Rules.Pattern

/-!
# Matching rule patterns

`RuleSpec.allMatches` finds every way the left-hand side of a rule matches a node,
and `RuleSpec.apply` turns a match into a certified rewrite: it builds the CPC
command list (an `evaluate` step per premise, then the rule) and runs it through
Logos's checker (`applyCmds`). This file is untrusted (see `Pattern.lean`).
-/

open Eo

namespace Telos

/-- What a pattern variable is bound to. -/
inductive Binding where
  | node (n : Node)
  /-- A run of children of an n-ary application of kind `k`. -/
  | list (k : Kind) (elems : List Node)
  deriving BEq, Inhabited

/-- A partial assignment of pattern variables. -/
abbrev Subst := Array (Option Binding)

/-- Bind variable `i` to `b`, or check that it is already bound to `b`. -/
def Subst.bind (σ : Subst) (i : Nat) (b : Binding) : List Subst :=
  match σ[i]? with
  | some none => [σ.set! i (some b)]
  | some (some b') => if b' == b then [σ] else []
  | none => []

mutual

/-- All extensions of `σ` under which `p` matches `n`. -/
partial def matchPat (σ : Subst) : Pat → Node → List Subst
  | .var i, n => σ.bind i (.node n)
  | .listVar _, _ => []
  | .const c, n => if n == .const c then [σ] else []
  | .app k ps, .app (.kind k') cs => if k == k' then matchList k σ ps cs.toList else []
  | .app _ _, _ => []

/-- All extensions of `σ` under which the patterns `ps` match the children `cs`
of an application of kind `k`. A list variable takes any run of children. -/
partial def matchList (k : Kind) (σ : Subst) : List Pat → List Node → List Subst
  | [], [] => [σ]
  | .listVar i :: ps, cs =>
      (List.range (cs.length + 1)).flatMap fun j =>
        (σ.bind i (.list k (cs.take j))).flatMap fun σ' => matchList k σ' ps (cs.drop j)
  | p :: ps, c :: cs => (matchPat σ p c).flatMap fun σ' => matchList k σ' ps cs
  | _ :: _, [] | [], _ :: _ => []

end

/-- The Logos term a binding stands for. A run of children of an n-ary operator
is the `:list` term Eunoia binds: the right-nested tail ending in the nil. -/
def Binding.toEo : Binding → Option Term
  | .node n => some n.toEo
  | .list k elems =>
    match k.eoShape with
    -- An empty run's nil would need the type of the elements, which a typed nil
    -- (`+`, `*`) is computed from; it is left stuck, and the step fails.
    | .rightAssocNil op nil =>
      let xs := elems.map Node.toEo
      some (eoRightAssocNil op (nil.eval op (xs.headD Term.Stuck)) xs)
    | _ => none

mutual

/-- The node a pattern stands for under a complete assignment. -/
partial def Pat.instantiate (σ : Subst) : Pat → Option Node
  | .var i => match σ[i]? with
    | some (some (.node n)) => some n
    | _ => none
  | .listVar _ => none
  | .const c => some (.const c)
  | .app k ps => do return .app (.kind k) (← Pat.instantiateList σ ps).toArray

/-- The children a list of patterns stands for; list variables are spliced in. -/
partial def Pat.instantiateList (σ : Subst) : List Pat → Option (List Node)
  | [] => some []
  | .listVar i :: ps => do
    match σ[i]? with
    | some (some (.list _ elems)) => return elems ++ (← Pat.instantiateList σ ps)
    | _ => none
  | p :: ps => do return (← p.instantiate σ) :: (← Pat.instantiateList σ ps)

end

namespace RuleSpec

/-- Every match of the rule's left-hand side against `n`. -/
def allMatches (r : RuleSpec) (n : Node) : List Subst :=
  matchPat (Array.replicate r.numVars none) r.lhs n

/-- `[k-1, …, 1, 0]`: the positions of `k` premises proven by the last `k` steps,
the first premise being the oldest. -/
def premiseIndices (k : Nat) : CIndexList :=
  (List.range k).foldl (fun acc i => .cons (Int.ofNat i) acc) .nil

/-- The CPC command list for applying the rule under the assignment `σ`. -/
def cmds (r : RuleSpec) (σ : Subst) : Option CCmdList := do
  let args ← r.args.mapM fun i => do (← σ[i]?.join).toEo
  let prems ← r.premises.mapM fun p => do return (← p.instantiate σ).toEo
  let evalSteps := prems.map fun a => CCmd.step .evaluate (.cons a .nil) .nil
  let ruleStep := CCmd.step r.rule (toArgList args) (premiseIndices prems.length)
  return (evalSteps ++ [ruleStep]).foldr .cons .nil

/-- Apply the rule to `n`: the first match whose command list Logos's checker
accepts. -/
def apply (r : RuleSpec) (n : Node) : Option (Rw n) :=
  r.allMatches n |>.findSome? fun σ => r.cmds σ >>= fun cs => applyCmds cs n

end RuleSpec

end Telos
