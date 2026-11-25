import Cpc.Logos
import Telos.Core.Node.SmtTypeFast

/-!
# Template rules

A template rule is a RARE rule whose Logos program builds its conclusion
`(= lhs rhs)` from its arguments, with no condition: `bool-double-not-elim`
takes `x` to `(= (not (not x)) x)`. telos builds the same two sides as nodes
(`TRule.lhs`, `TRule.rhs`), so a step by such a rule needs no run of Logos's
checker: `StaticProc.template` (`Telos/Core/Static.lean`) takes it under the
side condition `TRule.Ok`, decided without translating to Logos, and
`verification/TelosProofs/Core/Template.lean` proves the step is accepted.

To add a rule: a constructor, its `rule`, `ofRule`, `lhs` and `rhs` cases (and
`intArgs` if its program assumes integer arguments), and its case of
`TRule.step_eq` in the proof.
-/

open Eo
open Smtm

namespace Telos

/-- The template rules telos takes statically. -/
inductive TRule where
  | boolDoubleNotElim
  | arithElimLeq
  | arithElimLt
  | arithElimGt
  | arithLeqNorm
  | eqSymm
  | eqRefl
  deriving DecidableEq, Repr

namespace TRule

/-- The CPC rule. -/
def rule : TRule → CRule
  | .boolDoubleNotElim => .bool_double_not_elim
  | .arithElimLeq => .arith_elim_leq
  | .arithElimLt => .arith_elim_lt
  | .arithElimGt => .arith_elim_gt
  | .arithLeqNorm => .arith_leq_norm
  | .eqSymm => .eq_symm
  | .eqRefl => .eq_refl

/-- The template rule of a CPC rule, if it is one. -/
def ofRule : CRule → Option TRule
  | .bool_double_not_elim => some .boolDoubleNotElim
  | .arith_elim_leq => some .arithElimLeq
  | .arith_elim_lt => some .arithElimLt
  | .arith_elim_gt => some .arithElimGt
  | .arith_leq_norm => some .arithLeqNorm
  | .eq_symm => some .eqSymm
  | .eq_refl => some .eqRefl
  | _ => none

/-- The left-hand side, for the arguments `args`. -/
def lhs : TRule → List Node → Option Node
  | .boolDoubleNotElim, [x] => some (Node.notNode (Node.notNode x))
  | .arithElimLeq, [t, s] | .arithLeqNorm, [t, s] => some (Node.mkNode .LEQ #[t, s])
  | .arithElimLt, [t, s] => some (Node.mkNode .LT #[t, s])
  | .arithElimGt, [t, s] => some (Node.mkNode .GT #[t, s])
  | .eqSymm, [t, s] => some (Node.eqNode t s)
  | .eqRefl, [t] => some (Node.eqNode t t)
  | _, _ => none

/-- The right-hand side, for the arguments `args`. -/
def rhs : TRule → List Node → Option Node
  | .boolDoubleNotElim, [x] => some x
  | .arithElimLeq, [t, s] => some (Node.mkNode .GEQ #[s, t])
  | .arithElimLt, [t, s] => some (Node.notNode (Node.mkNode .GEQ #[t, s]))
  | .arithElimGt, [t, s] => some (Node.notNode (Node.mkNode .GEQ #[s, t]))
  | .arithLeqNorm, [t, s] =>
    some (Node.notNode (Node.mkNode .GEQ #[t, Node.mkNode .ADD #[s, .const (.integer 1)]]))
  | .eqSymm, [t, s] => some (Node.eqNode s t)
  | .eqRefl, [_] => some Node.mkTrue
  | _, _ => none

/-- Whether the program writes the integer `0` as the nil of a sum it builds
(`(+ s (+ 1 0))`), which is telos's sum only for an integer `s`. -/
def intArgs : TRule → Bool
  | .arithLeqNorm => true
  | _ => false

/-- The side condition of a step from `n` to `m` with the arguments `args`:
the sides are the rule's, the equation and the arguments are well typed, and
the arguments are integers where the program needs it. Decided by `smtTypeF`,
without translating to Logos. -/
def Ok (r : TRule) (args : List Node) (n m : Node) : Prop :=
  r.lhs args = some n ∧ r.rhs args = some m ∧ (Node.eqNode n m).smtTypeF = .Bool ∧
    (∀ a ∈ args, a.smtTypeF ≠ .None) ∧ (r.intArgs = true → ∀ a ∈ args, a.smtTypeF = .Int)

instance (r : TRule) (args : List Node) (n m : Node) : Decidable (r.Ok args n m) := by
  unfold Ok; infer_instance

/-- The arguments as a CPC argument list. -/
def argList : List Node → CArgList
  | [] => .nil
  | a :: as => .cons a.toEo (argList as)

/-- `[r args]`, then, with `rev`, `symm` of it: `(= rhs lhs)`. -/
def cmds (r : TRule) (args : List Node) (rev : Bool) : CCmdList :=
  .cons (.step r.rule (argList args) .nil)
    (if rev then .cons (.step .symm .nil (.cons 0 .nil)) .nil else .nil)

end TRule

end Telos
