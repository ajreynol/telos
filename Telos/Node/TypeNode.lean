import Telos.Node.Kind

/-!
# Types

cvc5 represents types as `TypeNode`s, which are nodes of type kinds
(`BOOLEAN_TYPE`, `BITVECTOR_TYPE`, `FUNCTION_TYPE`, `SORT_TYPE`, …). Here they are a
separate inductive with one constructor per type kind, so a type cannot be confused
with a term. The constructors cover the types that Logos gives a semantics to,
except datatypes and tuples, which come later.
-/

namespace Telos

inductive TypeNode where
  | boolean
  | integer
  | real
  /-- `String`, which is `(Seq Char)` in Logos. -/
  | string
  | regExp
  /-- Bit-vectors of width `width`. The width is an `Int`, as in Logos's
  `(BitVec w)`; a negative width is rejected by `Node.WellTyped`. -/
  | bitVector (width : Int)
  | array (index : TypeNode) (elem : TypeNode)
  | sequence (elem : TypeNode)
  | set (elem : TypeNode)
  /-- A function type `(-> arg range)`. As in Logos and Eunoia, `(-> A B C)` is
  curried to `(-> A (-> B C))`; `mkFunctionType` and `getArgTypes` give cvc5's
  flat view (`FUNCTION_TYPE` with children `A B C`). -/
  | function (arg : TypeNode) (range : TypeNode)
  /-- An uninterpreted sort (cvc5 `SORT_TYPE`). Logos numbers uninterpreted sorts
  (`Term.USort`), so the sort is identified by that number. -/
  | sort (id : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable, Ord

namespace TypeNode

def isBoolean : TypeNode → Bool
  | .boolean => true
  | _ => false

def isBitVector : TypeNode → Bool
  | .bitVector _ => true
  | _ => false

def isFunction : TypeNode → Bool
  | .function _ _ => true
  | _ => false

/-- cvc5's `NodeManager::mkFunctionType(args, range)`. -/
def mkFunctionType (args : List TypeNode) (range : TypeNode) : TypeNode :=
  args.foldr .function range

/-- cvc5's `getArgTypes`: the argument types of a (curried) function type. -/
def getArgTypes : TypeNode → List TypeNode
  | .function a r => a :: r.getArgTypes
  | _ => []

/-- cvc5's `getRangeType`. -/
def getRangeType : TypeNode → TypeNode
  | .function _ r => r.getRangeType
  | t => t

end TypeNode

end Telos

namespace Telos

/-- cvc5's `Theory::theoryOf(TypeNode)`: the theory that owns a type. -/
def TypeNode.theoryId : TypeNode → TheoryId
  | .boolean => .THEORY_BOOL
  | .integer | .real => .THEORY_ARITH
  | .bitVector _ => .THEORY_BV
  | .string | .regExp | .sequence _ => .THEORY_STRINGS
  | .array _ _ => .THEORY_ARRAYS
  | .set _ => .THEORY_SETS
  | .function _ _ | .sort _ => .THEORY_UF

end Telos
