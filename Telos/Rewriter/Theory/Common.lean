import Telos.Rewriter.Rules.Rules
import Telos.Core.Node.Order

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


/-- Rewrite by a named CPC rewrite rule. -/
def byRule (name : String) (n : Node) : Option (Rw n) := rewriteBy name n

/-- Rewrite `n`, the right-hand side of the template rule `r` with the
arguments `args`, to its left-hand side, statically (`StaticProc.template`). -/
def byTemplateRev (r : TRule) (args : List Node) (n : Node) : Option (Rw n) := do
  let m ← r.lhs args
  if h : Profile.time "static: side conditions" (fun _ => repr r |>.pretty)
      (fun _ => decide (r.Ok args m n)) = true then
    some ⟨m, .static (.template r args true) (show r.Ok args m n from of_decide_eq_true h) (.refl m)⟩
  else none

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
