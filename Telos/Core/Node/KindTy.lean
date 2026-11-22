import Telos.Core.Node.Kind
import Telos.Core.Node.TypeNode
import Cpc.SmtTyping

/-!
# Logos's typing rules, on the types of the children

The SMT type of an application, from the SMT types of its children, by the
rules of Logos's `__smtx_typeof`, for the kinds they cover (`kindTy`), and the
type of a free constant (`varTy`; `Const.ty` is that of a constant). They are below
`Node` so that each node can keep its type (`Node.fastTy`, a computed field),
as cvc5 keeps one in each node; `Telos/Core/Node/SmtTypeFast.lean` proves that
it is Logos's type of the node's translation.
-/


open Smtm
open SmtEval

namespace Telos

/-- `T` is `Bool`, and then `Bool`. -/
def boolTy1 (T : SmtType) : SmtType :=
  native_ite (native_Teq T SmtType.Bool) SmtType.Bool SmtType.None

/-- `T` and `U` are `Bool`, and then `Bool` (`and`, `or`, `=>`, `xor`). -/
def boolTy2 (T U : SmtType) : SmtType :=
  native_ite (native_Teq T SmtType.Bool)
    (native_ite (native_Teq U SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None

/-- The type of the nil of `+` or `*` for a first element of type `T`
(`typedNilOfType`): `0` or `1` of type `T` if it is arithmetic. -/
def arithNilTy : SmtType → SmtType
  | .Int => .Int
  | .Real => .Real
  | _ => .None

/-- The type of an application of the kind `k` to children of types `ts`, by
Logos's typing rules, for the kinds it covers. -/
def kindTy : Kind → List SmtType → Option SmtType
  | .NOT, [T] => some (boolTy1 T)
  | .IMPLIES, [T, U] | .XOR, [T, U] => some (boolTy2 T U)
  | .AND, ts@(_ :: _ :: _) | .OR, ts@(_ :: _ :: _) => some (ts.foldr boolTy2 .Bool)
  | .EQUAL, [T, U] => some (__smtx_typeof_eq T U)
  | .ITE, [C, T, U] => some (__smtx_typeof_ite C T U)
  | .ADD, ts@(T :: _ :: _) | .MULT, ts@(T :: _ :: _) =>
    some (ts.foldr __smtx_typeof_arith_overload_op_2 (arithNilTy T))
  | .SUB, [T, U] => some (__smtx_typeof_arith_overload_op_2 T U)
  | .NEG, [T] => some (__smtx_typeof_arith_overload_op_1 T)
  | .LT, [T, U] | .LEQ, [T, U] | .GT, [T, U] | .GEQ, [T, U] =>
    some (__smtx_typeof_arith_overload_op_2_ret T U .Bool)
  | .DIVISION, [T, U] => some (__smtx_typeof_arith_overload_op_2_ret T U .Real)
  | .TO_REAL, [T] => some (native_ite (native_Teq T .Int) .Real .None)
  | .STRING_LENGTH, [T] => some (__smtx_typeof_seq_op_1_ret T .Int)
  | .STRING_SUBSTR, [S, I, J] => some (__smtx_typeof_str_substr S I J)
  -- (strings only: the nil of a sequence of another element type is typed
  -- by its own rule)
  | .STRING_CONCAT, ts@(.Seq .Char :: _ :: _) => some (ts.foldr __smtx_typeof_seq_op_2 (.Seq .Char))
  | _, _ => none

/-- The SMT type of a free constant of type `T`, for the types `varTy` covers. -/
def varTy : TypeNode → Option SmtType
  | .boolean => some .Bool
  | .integer => some .Int
  | .real => some .Real
  | .string => some (.Seq .Char)
  | _ => none

end Telos
