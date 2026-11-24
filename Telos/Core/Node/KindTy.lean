import Telos.Core.Node.Kind
import Telos.Core.Node.TypeNode
import Telos.Core.Node.SkolemId
import Cpc.SmtTyping

/-!
# Logos's typing rules, on the types of the children

The SMT type of an application, from the SMT types of its children, by the
rules of Logos's `__smtx_typeof`, for the kinds they cover (`kindTy`), and the
type of a free constant (`varTy`; `Const.ty` is that of a constant). They are below
`Node` so that each node can keep its type (`Node.kept`, a computed field),
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

/-- `T` and `U` are regular expressions, and then a regular expression. -/
def reTy2 (T U : SmtType) : SmtType :=
  native_ite (native_Teq T .RegLan) (native_ite (native_Teq U .RegLan) .RegLan .None) .None

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
  | .ABS, [T] => some (__smtx_typeof_arith_overload_op_1 T)
  | .TO_INTEGER, [T] => some (native_ite (native_Teq T .Real) .Int .None)
  | .IS_INTEGER, [T] => some (native_ite (native_Teq T .Real) .Bool .None)
  | .INTS_DIVISION, [T, U] => some (native_ite (native_Teq T .Int) (native_ite (native_Teq U .Int) .Int .None) .None)
  | .INTS_MODULUS, [T, U] => some (native_ite (native_Teq T .Int) (native_ite (native_Teq U .Int) .Int .None) .None)
  | .INTS_DIVISION_TOTAL, [T, U] => some (native_ite (native_Teq T .Int) (native_ite (native_Teq U .Int) .Int .None) .None)
  | .INTS_MODULUS_TOTAL, [T, U] => some (native_ite (native_Teq T .Int) (native_ite (native_Teq U .Int) .Int .None) .None)
  | .DIVISIBLE, [T, U] => some (native_ite (native_Teq T .Int) (native_ite (native_Teq U .Int) .Bool .None) .None)
  | .STRING_UPDATE, [T, U, W] => some (__smtx_typeof_str_update T U W)
  | .STRING_CHARAT, [T, U] => some (__smtx_typeof_str_at T U)
  | .STRING_CONTAINS, [T, U] => some (__smtx_typeof_seq_op_2_ret T U .Bool)
  | .STRING_PREFIX, [T, U] => some (__smtx_typeof_seq_op_2_ret T U .Bool)
  | .STRING_SUFFIX, [T, U] => some (__smtx_typeof_seq_op_2_ret T U .Bool)
  | .STRING_LT, [T, U] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U (.Seq .Char)) .Bool .None) .None)
  | .STRING_LEQ, [T, U] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U (.Seq .Char)) .Bool .None) .None)
  | .STRING_INDEXOF, [T, U, W] => some (__smtx_typeof_str_indexof T U W)
  | .STRING_INDEXOF_RE, [T, U, W] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U .RegLan) (native_ite (native_Teq W .Int) .Int .None) .None) .None)
  | .STRING_REPLACE, [T, U, W] => some (__smtx_typeof_seq_op_3 T U W)
  | .STRING_REPLACE_ALL, [T, U, W] => some (__smtx_typeof_seq_op_3 T U W)
  | .STRING_REPLACE_RE, [T, U, W] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U .RegLan) (native_ite (native_Teq W (.Seq .Char)) ((.Seq .Char)) .None) .None) .None)
  | .STRING_REPLACE_RE_ALL, [T, U, W] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U .RegLan) (native_ite (native_Teq W (.Seq .Char)) ((.Seq .Char)) .None) .None) .None)
  | .STRING_IS_DIGIT, [T] => some (native_ite (native_Teq T (.Seq .Char)) .Bool .None)
  | .STRING_ITOS, [T] => some (native_ite (native_Teq T .Int) ((.Seq .Char)) .None)
  | .STRING_STOI, [T] => some (native_ite (native_Teq T (.Seq .Char)) .Int .None)
  | .STRING_TO_CODE, [T] => some (native_ite (native_Teq T (.Seq .Char)) .Int .None)
  | .STRING_FROM_CODE, [T] => some (native_ite (native_Teq T .Int) ((.Seq .Char)) .None)
  | .STRING_TO_LOWER, [T] => some (native_ite (native_Teq T (.Seq .Char)) ((.Seq .Char)) .None)
  | .STRING_TO_UPPER, [T] => some (native_ite (native_Teq T (.Seq .Char)) ((.Seq .Char)) .None)
  | .STRING_REV, [T] => some (__smtx_typeof_seq_op_1 T)
  | .STRING_TO_REGEXP, [T] => some (native_ite (native_Teq T (.Seq .Char)) .RegLan .None)
  | .STRING_IN_REGEXP, [T, U] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U .RegLan) .Bool .None) .None)
  | .REGEXP_NONE, [] => some .RegLan
  | .REGEXP_ALL, [] => some .RegLan
  | .REGEXP_ALLCHAR, [] => some .RegLan
  | .REGEXP_DIFF, [T, U] => some (native_ite (native_Teq T .RegLan) (native_ite (native_Teq U .RegLan) .RegLan .None) .None)
  | .REGEXP_STAR, [T] => some (native_ite (native_Teq T .RegLan) .RegLan .None)
  | .REGEXP_PLUS, [T] => some (native_ite (native_Teq T .RegLan) .RegLan .None)
  | .REGEXP_OPT, [T] => some (native_ite (native_Teq T .RegLan) .RegLan .None)
  | .REGEXP_RANGE, [T, U] => some (native_ite (native_Teq T (.Seq .Char)) (native_ite (native_Teq U (.Seq .Char)) .RegLan .None) .None)
  | .REGEXP_COMPLEMENT, [T] => some (native_ite (native_Teq T .RegLan) .RegLan .None)
  | .REGEXP_CONCAT, ts@(_ :: _ :: _) | .REGEXP_INTER, ts@(_ :: _ :: _) | .REGEXP_UNION, ts@(_ :: _ :: _) =>
    some (ts.foldr reTy2 .RegLan)
  | _, _ => none

/-- The type a node keeps: none, its own, or, for a skolem that is a function (it has
no type of its own in Logos), those of its argument and result. -/
inductive KeptTy where
  | none
  | ty (T : SmtType)
  | fn (arg res : SmtType)
  deriving Inhabited

namespace KeptTy

def ty? : KeptTy → Option SmtType
  | .ty T => some T
  | _ => Option.none

def ofOption : Option SmtType → KeptTy
  | some T => .ty T
  | Option.none => .none

/-- The type of `(f t)`, from what `f` and `t` keep. -/
def apply : KeptTy → List SmtType → KeptTy
  | .fn A R, [T] => if T = A then .ty R else .none
  | _, _ => .none

end KeptTy

/-- What a skolem keeps, from the types of its cache values. -/
def skolemTy : SkolemId → List SmtType → KeptTy
  -- the purification skolem `(@purify t)` has the type of `t`
  | .PURIFY, [T] => .ty T
  | .INT_DIV_BY_ZERO, [] | .MOD_BY_ZERO, [] => .fn .Int .Int
  | .STRINGS_STOI_NON_DIGIT, [.Seq .Char] => .ty .Int
  | .STRINGS_NUM_OCCUR, [.Seq .Char, .Seq .Char] => .ty .Int
  | .STRINGS_NUM_OCCUR_RE, [.Seq .Char, .RegLan] => .ty .Int
  | .STRINGS_STOI_RESULT, [.Seq .Char] => .fn .Int .Int
  | .STRINGS_ITOS_RESULT, [.Int] => .fn .Int .Int
  | .STRINGS_OCCUR_INDEX, [.Seq .Char, .Seq .Char] => .fn .Int .Int
  | .STRINGS_OCCUR_INDEX_RE, [.Seq .Char, .RegLan] => .fn .Int .Int
  | .STRINGS_REPLACE_ALL_RESULT, [.Seq .Char, .Seq .Char, .Seq .Char] => .fn .Int (.Seq .Char)
  | .STRINGS_REPLACE_RE_ALL_RESULT, [.Seq .Char, .RegLan, .Seq .Char] => .fn .Int (.Seq .Char)
  | _, _ => .none

/-- The type of an application of an indexed kind. -/
def indexedTy : Kind → List Int → List SmtType → Option SmtType
  | .REGEXP_REPEAT, [i], [.RegLan] => if 0 ≤ i then some .RegLan else none
  | .REGEXP_LOOP, [i, j], [.RegLan] => if 0 ≤ i ∧ 0 ≤ j then some .RegLan else none
  | _, _, _ => none

/-- The SMT type of a free constant of type `T`, for the types `varTy` covers. -/
def varTy : TypeNode → Option SmtType
  | .boolean => some .Bool
  | .integer => some .Int
  | .real => some .Real
  | .string => some (.Seq .Char)
  | _ => none

end Telos
