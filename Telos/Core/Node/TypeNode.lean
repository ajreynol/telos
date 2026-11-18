import Telos.Core.Node.Kind

/-!
# Types

cvc5 represents types as `TypeNode`s, which are nodes of type kinds
(`BOOLEAN_TYPE`, `BITVECTOR_TYPE`, `FUNCTION_TYPE`, `SORT_TYPE`, …). Here they are a
separate inductive with one constructor per type kind, so a type cannot be confused
with a term. The constructors cover the types that Logos gives a semantics to.
Parametric datatypes need no constructor: Logos's parser instantiates them, and
each instance is a datatype of its own (named `.par_k_D`).

Datatypes mirror Logos's `Term.DatatypeType` exactly: a datatype is its name and
the whole block of (mutually recursive) datatypes it was declared in, each a list
of constructors, each a list of field types, in which the block's own datatypes
are `typeRef`s. Constructors and selectors have no names here, as in Logos;
their names are only for printing (`DtNames`, `Telos/Core/Node/Print.lean`).
-/

namespace Telos

mutual

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
  /-- The datatype `name` of the block `decl` (cvc5 `DATATYPE_TYPE`; Logos's
  `Term.DatatypeType`). -/
  | datatype (name : String) (decl : DtDecl)
  /-- Inside a block, a reference to one of its datatypes (Logos's
  `Term.DatatypeTypeRef`). -/
  | typeRef (name : String)
  /-- The tuple type with no fields (Logos's `UnitTuple`). -/
  | unitTuple
  /-- The tuple type with first field `head` and the fields of the tuple type
  `rest` after it, as Eunoia writes `(Tuple T₁ … Tₙ)`: `(Tuple T₁ (Tuple T₂ …
  UnitTuple))` (Logos's `Tuple`, a `:right-assoc-nil` type constructor). -/
  | tuple (head : TypeNode) (rest : TypeNode)

/-- A block of datatypes, by name (Logos's `DatatypeDecl`). -/
inductive DtDecl where
  | nil
  | cons (name : String) (dt : Dt) (rest : DtDecl)

/-- The constructors of a datatype (Logos's `Datatype`). -/
inductive Dt where
  | null
  | sum (c : DtCons) (rest : Dt)

/-- The field types of a constructor (Logos's `DatatypeCons`). -/
inductive DtCons where
  | unit
  | cons (field : TypeNode) (rest : DtCons)

end

deriving instance DecidableEq, Repr, Inhabited, Hashable, Ord for TypeNode, DtDecl, Dt, DtCons

namespace DtDecl

/-- The datatype of this name. -/
def lookup? : DtDecl → String → Option Dt
  | .nil, _ => none
  | .cons n d rest, s => if n == s then some d else rest.lookup? s

end DtDecl

namespace Dt

def toList : Dt → List DtCons
  | .null => []
  | .sum c rest => c :: rest.toList

def numConstructors (d : Dt) : Nat := d.toList.length

end Dt

def DtCons.toList : DtCons → List TypeNode
  | .unit => []
  | .cons f rest => f :: rest.toList

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

def isDatatype : TypeNode → Bool
  | .datatype .. => true
  | _ => false

/-- The field types of a tuple type. -/
def tupleFields? : TypeNode → Option (List TypeNode)
  | .unitTuple => some []
  | .tuple h rest => (h :: ·) <$> rest.tupleFields?
  | _ => none

/-- The tuple type with these fields. -/
def mkTuple (fields : List TypeNode) : TypeNode := fields.foldr .tuple .unitTuple

/-- The constructors of a datatype type. -/
def dtConstructors? : TypeNode → Option (List DtCons)
  | .datatype s decl => (decl.lookup? s).map Dt.toList
  | _ => none

/-- A field type of a constructor of the datatype block `decl`, with a reference
to one of the block's datatypes resolved to that datatype. -/
def resolveIn (decl : DtDecl) : TypeNode → TypeNode
  | .typeRef r => .datatype r decl
  | T => T

/-- The field types of constructor `i` of a datatype type, resolved. -/
def dtFields? (T : TypeNode) (i : Nat) : Option (List TypeNode) := do
  let .datatype _ decl := T | none
  let c ← (← T.dtConstructors?)[i]?
  return c.toList.map (resolveIn decl)

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
  | .datatype .. | .typeRef _ | .unitTuple | .tuple .. => .THEORY_DATATYPES

end Telos
