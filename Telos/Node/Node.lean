import Telos.Node.Kind
import Telos.Node.TypeNode

/-!
# Nodes

The term datatype, modelled on cvc5's `Node`: a kind plus n-ary children
(`NodeValue`), with constants carrying a payload of their own (`getConst<T>()`).

Differences from cvc5, on purpose:

* No hash-consing through a `NodeManager`. `Node` is a plain tree with structural
  equality, so the specification does not depend on a global table's invariants.
  Speed comes later from a cached hash, physical sharing (Lean's `ShareCommon`)
  and a rewrite cache.
* Free constants carry their name and type in the node instead of in the
  `NodeManager`'s attribute table.
* The operator of an application is an `Op`: a kind, or a kind with integer
  indices for parameterized kinds such as `BITVECTOR_EXTRACT`. This is the form of
  cvc5's API `Op`; internally cvc5 stores the indices in an operator node
  (`getOperator()`).

Numeric payloads (bit-vector widths and values, indices) use the types Logos uses,
which is `Int` throughout, so `toEo` copies them unchanged. Values that are out of
range (a negative width, a value `≥ 2 ^ width`, `hi < lo` for extract) are not
excluded by the datatype; they are rejected by `Node.WellTyped`.
-/

namespace Telos

/-- Constant payloads (cvc5's `Rational`, `BitVector`, and so on). -/
inductive Const where
  | boolean (b : Bool)
  | integer (n : Int)
  | rational (q : Rat)
  /-- A bit-vector of width `width` with value `value`, as Logos's
  `Term.Binary`. Well typed only when `0 ≤ width` and `0 ≤ value < 2 ^ width`. -/
  | bitVector (width : Int) (value : Int)
  deriving DecidableEq, Repr, Inhabited

namespace Const

def kind : Const → Kind
  | .boolean _ => .CONST_BOOLEAN
  | .integer _ => .CONST_INTEGER
  | .rational _ => .CONST_RATIONAL
  | .bitVector _ _ => .CONST_BITVECTOR

end Const

/-- The operator of an application (cvc5's API `Op`). -/
inductive Op where
  /-- An operator kind with no indices, such as `AND`. -/
  | kind (k : Kind)
  /-- A parameterized kind with its indices, such as `((_ extract 7 4) x)`, which
  is `indexed BITVECTOR_EXTRACT #[7, 4]`. -/
  | indexed (k : Kind) (indices : Array Int)
  deriving DecidableEq, Repr, Inhabited

namespace Op

def getKind : Op → Kind
  | .kind k => k
  | .indexed k _ => k

/-- The indices of a parameterized operator; empty for other operators. -/
def getIndices : Op → Array Int
  | .kind _ => #[]
  | .indexed _ is => is

end Op

inductive Node where
  /-- A constant (cvc5 `CONST_*` kinds). -/
  | const (c : Const)
  /-- A free constant (cvc5 `VARIABLE`), with its name and type. -/
  | var (name : String) (type : TypeNode)
  /-- An operator application with n-ary children, as in cvc5. -/
  | app (op : Op) (children : Array Node)
  deriving Inhabited, Repr

namespace Node

def getKind : Node → Kind
  | .const c => c.kind
  | .var _ _ => .VARIABLE
  | .app op _ => op.getKind

/-- The operator of an application (cvc5's `getOperator()`), if any. -/
def getOperator? : Node → Option Op
  | .app op _ => some op
  | _ => none

/-- The children of a node. Constants and variables have none. -/
def getChildren : Node → Array Node
  | .app _ cs => cs
  | _ => #[]

def getNumChildren (n : Node) : Nat := n.getChildren.size

def isConst : Node → Bool
  | .const _ => true
  | _ => false

def isVar : Node → Bool
  | .var _ _ => true
  | _ => false

/-- The Boolean value of a `CONST_BOOLEAN` node. -/
def getConstBoolean? : Node → Option Bool
  | .const (.boolean b) => some b
  | _ => none

/-! ## Construction, after `NodeManager::mk*` -/

def mkConst (c : Const) : Node := .const c
def mkVar (name : String) (type : TypeNode) : Node := .var name type
def mkNode (k : Kind) (children : Array Node) : Node := .app (.kind k) children
def mkIndexedNode (k : Kind) (indices : Array Int) (children : Array Node) : Node :=
  .app (.indexed k indices) children

def mkTrue : Node := .const (.boolean true)
def mkFalse : Node := .const (.boolean false)
def mkBool (b : Bool) : Node := .const (.boolean b)

def notNode (n : Node) : Node := mkNode .NOT #[n]
def eqNode (a b : Node) : Node := mkNode .EQUAL #[a, b]
def andNode (a b : Node) : Node := mkNode .AND #[a, b]
def orNode (a b : Node) : Node := mkNode .OR #[a, b]
def iteNode (c t e : Node) : Node := mkNode .ITE #[c, t, e]
def extractNode (hi lo : Int) (x : Node) : Node :=
  mkIndexedNode .BITVECTOR_EXTRACT #[hi, lo] #[x]

end Node

end Telos
