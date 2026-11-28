import Cpc.Logos
import Telos.Core.Node.SmtTypeFast

/-!
# Evaluation of an operator over constants

The `evaluate` rule takes a term to its value, computed by Logos's program
`__run_evaluate`. Most of telos's uses of it are one operator applied to
constants, such as `(str.len "abc")` or `(+ 1 2)`. `value` computes those
natively, and `StaticProc.evalConst` (`Telos/Core/Static.lean`) takes the step
without running Logos's checker: `verification/TelosProofs/Core/EvalConst.lean`
proves that `__run_evaluate` returns the translation of `value n`. Other terms
are evaluated by running the checker (`byEvaluate`).

The operators: `not` of a Boolean; `=` of two constants of the same kind
(Booleans, integers, rationals or strings); `>=` of two integers or two
rationals; `+` of integers or of rationals; `str.++` and `str.len` of strings,
and `str.contains` of two strings.
-/

namespace Telos.EvalConst

/-- The integers of `cs`, if they are all integer constants. -/
def ints : List Node → Option (List Int)
  | [] => some []
  | .const (.integer i) :: cs => (ints cs).map (i :: ·)
  | _ => none

/-- The rationals of `cs`, if they are all rational constants. -/
def rats : List Node → Option (List Rat)
  | [] => some []
  | .const (.rational q) :: cs => (rats cs).map (q :: ·)
  | _ => none

/-- The strings of `cs`, if they are all string constants. -/
def strs : List Node → Option (List (List Nat))
  | [] => some []
  | .const (.string s) :: cs => (strs cs).map (s :: ·)
  | _ => none

/-- Whether two constants are of the same kind that `=` is evaluated on. -/
def sameKind : Const → Const → Bool
  | .boolean _, .boolean _ | .integer _, .integer _ | .rational _, .rational _
  | .string _, .string _ => true
  | _, _ => false

/-- A Boolean constant. -/
def bool (b : Bool) : Node := .const (.boolean b)

/-- The value of an operator `k` over the constants `cs`. -/
def valueOf : Kind → List Node → Option Node
  | .NOT, [.const (.boolean b)] => some (bool !b)
  | .EQUAL, [.const a, .const b] => if sameKind a b then some (bool (decide (a = b))) else none
  | .GEQ, [.const (.integer a), .const (.integer b)] => some (bool (decide (b ≤ a)))
  | .GEQ, [.const (.rational a), .const (.rational b)] => some (bool (decide (b ≤ a)))
  | .STRING_LENGTH, [.const (.string s)] => some (.const (.integer s.length))
  | .STRING_CONTAINS, [.const (.string s), .const (.string t)] =>
    some (bool (decide (0 ≤ Eo.native_str_indexof s t 0)))
  | .ADD, cs@(_ :: _ :: _) =>
    match ints cs with
    | some is => some (.const (.integer is.sum))
    | none => (rats cs).map fun qs => .const (.rational qs.sum)
  | .STRING_CONCAT, cs@(_ :: _ :: _) => (strs cs).map fun ss => .const (.string ss.flatten)
  | _, _ => none

/-- The value of `n`, an operator over constants. -/
def value : Node → Option Node
  | .app (.kind k) cs => valueOf k cs.toList
  | _ => none

/-- The side condition of a step from `n` to its value `m`: `m` is the value,
and `(= n m)` is well typed. -/
def Ok (n m : Node) : Prop := value n = some m ∧ (Node.eqNode n m).smtTypeF = .Bool

instance (n m : Node) : Decidable (Ok n m) := by unfold Ok; infer_instance

end Telos.EvalConst
