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
* Parameterized kinds (`BITVECTOR_EXTRACT` and so on) are not supported yet. In
  cvc5 their indices live in an operator node (`getOperator()`); here they will be
  an extra payload on `app`.
-/

namespace Telos

/-- Constant payloads (cvc5's `Rational`, `BitVector`, and so on). -/
inductive Const where
  | boolean (b : Bool)
  | integer (n : Int)
  | rational (q : Rat)
  /-- A bit-vector of width `width` with value `value`. Well typed only when
  `value < 2 ^ width`. -/
  | bitVector (width : Nat) (value : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Const

def kind : Const → Kind
  | .boolean _ => .CONST_BOOLEAN
  | .integer _ => .CONST_INTEGER
  | .rational _ => .CONST_RATIONAL
  | .bitVector _ _ => .CONST_BITVECTOR

end Const

inductive Node where
  /-- A constant (cvc5 `CONST_*` kinds). -/
  | const (c : Const)
  /-- A free constant (cvc5 `VARIABLE`), with its name and type. -/
  | var (name : String) (type : TypeNode)
  /-- An operator application with n-ary children, as in cvc5. -/
  | app (k : Kind) (children : Array Node)
  deriving Inhabited, Repr

namespace Node

def getKind : Node → Kind
  | .const c => c.kind
  | .var _ _ => .VARIABLE
  | .app k _ => k

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
def mkNode (k : Kind) (children : Array Node) : Node := .app k children

def mkTrue : Node := .const (.boolean true)
def mkFalse : Node := .const (.boolean false)
def mkBool (b : Bool) : Node := .const (.boolean b)

def notNode (n : Node) : Node := mkNode .NOT #[n]
def eqNode (a b : Node) : Node := mkNode .EQUAL #[a, b]
def andNode (a b : Node) : Node := mkNode .AND #[a, b]
def orNode (a b : Node) : Node := mkNode .OR #[a, b]
def iteNode (c t e : Node) : Node := mkNode .ITE #[c, t, e]

end Node

end Telos
