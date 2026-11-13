import Telos.Rules.Rules
import Telos.Node.Order

/-!
# Building certified rewrites

Combinators for theory strategies. A strategy decides, as cvc5 does, what a node
should rewrite to. Every change it makes is a CPC step, so the result is
`Certified` and needs no proof. When a step it expects to apply is rejected by
the checker, the combinators keep the result so far, which is sound but may
differ from cvc5. Fuzzing against cvc5 finds such cases.
-/

open Eo

namespace Telos

/-- A certified rewrite of `n`. -/
abbrev Rw (n : Node) := { m // Certified n m }

namespace Rw

/-- No rewrite. -/
def id (n : Node) : Rw n := ⟨n, .refl n⟩

/-- Continue a rewrite with a step on its result. If the step does not apply,
stop where we are. -/
def next {n : Node} (r : Rw n) (f : (m : Node) → Option (Rw m)) : Rw n :=
  match f r.1 with
  | some ⟨k, h⟩ => ⟨k, r.2.trans h⟩
  | none => r

/-- Like `next`, but fail if the step does not apply. -/
def next? {n : Node} (r : Rw n) (f : (m : Node) → Option (Rw m)) : Option (Rw n) :=
  (f r.1).map fun ⟨k, h⟩ => ⟨k, r.2.trans h⟩

instance (n : Node) : Inhabited (Rw n) := ⟨id n⟩

/-- Rewrite child `i` of `n` by `f`, when `n` is an application whose operator is
congruent in its children, and all its children are well typed. -/
def congrArg (n : Node) (i : Nat) (f : (c : Node) → Option (Rw c)) : Option (Rw n) :=
  match n with
  | .app op cs =>
    if hi : i < cs.size then
      if hop : op.eoShape.isChildCongruent = true then
        if hwt : ∀ c ∈ cs.toList, c.WellTyped then
          (f cs[i]).map fun ⟨c', hc⟩ =>
            ⟨.app op (cs.set i c'), .congrArg i c' hi hop hwt hc (.refl _)⟩
        else none
      else none
    else none
  | _ => none

end Rw

/-- Rewrite by a named CPC rewrite rule. -/
def byRule (name : String) (n : Node) : Option (Rw n) := rewriteBy name n

/-- Rewrite `n` to `m`, validated by a CPC rule that takes the equation
`(= n m)` as its argument (for example `aci_norm` or `absorb`). This is how
results computed by unverified code are certified. -/
def checkBy (r : CRule) (n m : Node) : Option (Rw n) :=
  applyCmds (.cons (.step r (.cons (eqFormula n m) .nil) .nil) .nil) n

/-- Rewrite `n` to its value, by the `evaluate` rule. -/
def byEvaluate (n : Node) : Option (Rw n) :=
  applyCmds (.cons (.step .evaluate (.cons n.toEo .nil) .nil) .nil) n

/-- Rewrite `n` by the rule `r` with the given arguments, whose premises are
proven by `premiseSteps`, in order (one step per premise). For premises that
`evaluate` cannot prove, for example `(= (not (not b)) b)` by
`bool-double-not-elim`. -/
def byRuleWithPremises (r : CRule) (args : List Node) (premiseSteps : List CCmd) (n : Node) :
    Option (Rw n) :=
  let ruleStep := CCmd.step r (toArgList (args.map Node.toEo))
    (RuleSpec.premiseIndices premiseSteps.length)
  applyCmds ((premiseSteps ++ [ruleStep]).foldr .cons .nil) n

/-- The CPC step `(rule args)` with no premises. -/
def stepCmd (r : CRule) (args : List Node) : CCmd :=
  .step r (toArgList (args.map Node.toEo)) .nil

/-- Try the steps in order; the first that applies. -/
def firstOf {n : Node} : List (Unit → Option (Rw n)) → Option (Rw n)
  | [] => none
  | f :: fs => (f ()).orElse fun _ => firstOf fs

end Telos
