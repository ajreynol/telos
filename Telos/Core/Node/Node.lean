import Telos.Core.Node.Kind
import Telos.Core.Node.TypeNode
import Telos.Core.Node.SkolemId

/-!
# Nodes

The term datatype, modelled on cvc5's `Node`. Its shape follows cvc5's metakinds,
so that adding a theory only adds `Kind`s and `toEo` cases, never new `Node`
constructors:

| cvc5 metakind                  | here                                  |
|--------------------------------|---------------------------------------|
| `CONSTANT` (`CONST_*`)         | `const c`                             |
| `VARIABLE` (free constants)    | `var name type`                       |
| `VARIABLE` (`BOUND_VARIABLE`)  | `boundVar name type`                  |
| `VARIABLE` (`SKOLEM`)          | `skolem id cacheVals`                 |
| `OPERATOR`                     | `app (.kind k) children`              |
| `PARAMETERIZED`, indexed       | `app (.indexed k indices) children`   |
| `PARAMETERIZED`, term operator | `app (.node k f) children`            |

A skolem is atomic, as in cvc5, where it is a variable: its cache values are
not children, so traversals of children (rewriting, congruence, substitution)
do not enter it. Its meaning is that of its CPC term (`(@purify t)`), so the
functions that must see the cache values (`toEo`, `vars`, printing) handle
`skolem` explicitly. Skolems that are functions, such as `@int_div_by_zero`,
are applied with `APPLY_UF`, as in cvc5, and their arguments are children.

Binders follow cvc5: `FORALL` has children `[BOUND_VAR_LIST(x₁ … xₙ), body]`,
optionally followed by an `INST_PATTERN_LIST`.

Differences from cvc5, on purpose:

* No hash-consing through a `NodeManager`. `Node` is a plain tree with structural
  equality, so the specification does not depend on a global table's invariants.
* Variables carry their name and type in the node instead of in the
  `NodeManager`'s attribute table. Two variables with the same name and type are
  the same variable, as they are in Logos. cvc5 instead distinguishes variables by
  identity, so code that creates fresh variables must pick fresh names.
* `Op` is cvc5's API `Op`. Internally cvc5 stores a parameterized kind's operator
  as an extra first child (`getOperator()`).

Numeric payloads (bit-vector widths and values, indices) use the types Logos uses,
`Int`, so `toEo` copies them unchanged. Values that are out of range (a negative
width, a value `≥ 2 ^ width`, `hi < lo` for extract) are not excluded by the
datatype; `Node.WellTyped` rejects them.
-/

namespace Telos

/-- Constant payloads (cvc5's `Rational`, `BitVector`, `String`, and so on). -/
inductive Const where
  | boolean (b : Bool)
  | integer (n : Int)
  | rational (q : Rat)
  /-- A bit-vector of width `width` with value `value`, as Logos's
  `Term.Binary`. Well typed only when `0 ≤ width` and `0 ≤ value < 2 ^ width`. -/
  | bitVector (width : Int) (value : Int)
  /-- A string, as a list of code points (cvc5's `String`, Logos's
  `native_String`). Well typed only when every code point is valid. -/
  | string (codePoints : List Nat)
  /-- The empty set whose elements have type `elem` (cvc5's `EmptySet`, of type
  `(Set elem)`). -/
  | emptySet (elem : TypeNode)
  /-- Constructor `index` of the datatype `dt` (Logos's `Term.DtCons`). It is the
  operator of `APPLY_CONSTRUCTOR` and `APPLY_TESTER` applications. -/
  | dtCons (dt : TypeNode) (index : Nat)
  /-- Selector `sel` of constructor `cons` of the datatype `dt` (Logos's
  `Term.DtSel`). It is the operator of `APPLY_SELECTOR` and `APPLY_UPDATER`
  applications. -/
  | dtSel (dt : TypeNode) (cons sel : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Const

def kind : Const → Kind
  | .boolean _ => .CONST_BOOLEAN
  | .integer _ => .CONST_INTEGER
  | .rational _ => .CONST_RATIONAL
  | .bitVector _ _ => .CONST_BITVECTOR
  | .string _ => .CONST_STRING
  | .emptySet _ => .SET_EMPTY
  | .dtCons .. | .dtSel .. => .DT_SYMBOL

/-- A string constant from a Lean string. -/
def ofString (s : String) : Const := .string (s.toList.map Char.toNat)

end Const

mutual

inductive Node where
  /-- A constant (cvc5 `CONST_*` kinds). -/
  | const (c : Const)
  /-- A free constant or function symbol (cvc5 `VARIABLE`). -/
  | var (name : String) (type : TypeNode)
  /-- A bound variable (cvc5 `BOUND_VARIABLE`). -/
  | boundVar (name : String) (type : TypeNode)
  /-- A skolem (cvc5 `SKOLEM`): `SkolemManager::mkSkolemFunction id cacheVals`.
  Two skolems are the same when their identifiers and cache values are, as in
  cvc5's skolem cache. Its type is determined by them (`typeHint`). -/
  | skolem (id : SkolemId) (cacheVals : Array Node)
  /-- An operator application with n-ary children, as in cvc5. -/
  | app (op : Op) (children : Array Node)

/-- The operator of an application (cvc5's API `Op`). -/
inductive Op where
  /-- An operator kind with no payload, such as `AND`. -/
  | kind (k : Kind)
  /-- A parameterized kind with integer indices: `((_ extract 7 4) x)` is
  `app (.indexed BITVECTOR_EXTRACT #[7, 4]) #[x]`. -/
  | indexed (k : Kind) (indices : Array Int)
  /-- A parameterized kind whose operator is a term: `(f a b)` is
  `app (.node APPLY_UF f) #[a, b]`. -/
  | node (k : Kind) (op : Node)

end

deriving instance BEq, Hashable, Repr for Node

instance : Inhabited Node := ⟨.const (.boolean false)⟩
instance : Inhabited Op := ⟨.kind .EQUAL⟩

namespace Op

def getKind : Op → Kind
  | .kind k => k
  | .indexed k _ => k
  | .node k _ => k

/-- The indices of an indexed operator; empty for other operators. -/
def getIndices : Op → Array Int
  | .indexed _ is => is
  | _ => #[]

end Op

namespace Node

def getKind : Node → Kind
  | .const c => c.kind
  | .var _ _ => .VARIABLE
  | .boundVar _ _ => .BOUND_VARIABLE
  | .skolem _ _ => .SKOLEM
  | .app op _ => op.getKind

/-- The operator of an application (cvc5's `getOperator()`), if any. -/
def getOperator? : Node → Option Op
  | .app op _ => some op
  | _ => none

/-- The children of a node. Constants and variables have none. As in cvc5, the
operator of a parameterized kind is not a child. -/
def getChildren : Node → Array Node
  | .app _ cs => cs
  | _ => #[]

def getNumChildren (n : Node) : Nat := n.getChildren.size

/-- cvc5's `isConst`: a constant, or a constructor applied to constants. -/
def isConst : Node → Bool
  | .const _ => true
  | .app (.node .APPLY_CONSTRUCTOR _) cs => cs.attach.all fun ⟨c, _⟩ => isConst c
  -- a tuple of constants (cvc5's tuples are datatypes), and a singleton set of
  -- a constant (a set value, which cvc5 treats as a constant)
  | .app (.kind k) cs =>
    (k == .TUPLE || k == .TUPLE_UNIT || k == .SET_SINGLETON) && cs.attach.all fun ⟨c, _⟩ => isConst c
  | _ => false

/-- cvc5's `isVar`: a node of metakind `VARIABLE`, so a free or bound variable, or
a skolem. -/
def isVar : Node → Bool
  | .var _ _ | .boundVar _ _ | .skolem _ _ => true
  | _ => false

/-- The Boolean value of a `CONST_BOOLEAN` node. -/
def getConstBoolean? : Node → Option Bool
  | .const (.boolean b) => some b
  | _ => none

/-! ## Construction, after `NodeManager::mk*` -/

def mkConst (c : Const) : Node := .const c
def mkVar (name : String) (type : TypeNode) : Node := .var name type
def mkBoundVar (name : String) (type : TypeNode) : Node := .boundVar name type
def mkSkolem (id : SkolemId) (cacheVals : Array Node) : Node := .skolem id cacheVals
/-- The purification skolem of `t` (`SkolemManager::mkPurifySkolem`). -/
def mkPurifySkolem (t : Node) : Node := .skolem .PURIFY #[t]
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
def applyUF (f : Node) (args : Array Node) : Node := .app (.node .APPLY_UF f) args
def forallNode (vars : Array Node) (body : Node) : Node :=
  mkNode .FORALL #[mkNode .BOUND_VAR_LIST vars, body]
def existsNode (vars : Array Node) (body : Node) : Node :=
  mkNode .EXISTS #[mkNode .BOUND_VAR_LIST vars, body]

end Node

end Telos
