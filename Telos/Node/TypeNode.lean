/-!
# Types

cvc5 represents types as `TypeNode`s built by the `NodeManager`
(`booleanType()`, `integerType()`, `realType()`, `mkBitVectorType(w)`). They are
kept as a separate inductive here, since types and terms are not mixed in the
kinds covered so far.
-/

namespace Telos

inductive TypeNode where
  | boolean
  | integer
  | real
  /-- Bit-vectors of width `width`. The width is an `Int`, as in Logos's
  `(BitVec w)`; a negative width is rejected by `Node.WellTyped`. -/
  | bitVector (width : Int)
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace TypeNode

def isBoolean : TypeNode → Bool
  | .boolean => true
  | _ => false

def isBitVector : TypeNode → Bool
  | .bitVector _ => true
  | _ => false

end TypeNode

end Telos
