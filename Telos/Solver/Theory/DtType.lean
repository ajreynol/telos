import Telos.Core.Node.FastType
import Telos.Core.Node.Key

/-!
# Datatype types and terms, for the theory of datatypes

What cvc5's theory of datatypes (`src/theory/datatypes/`) asks of a datatype
type (`DType`, `src/expr/dtype.cpp`) and the terms it builds
(`theory_datatypes_utils.cpp`):
- cardinality classes (`CardinalityClass`, `TypeNode::getCardinalityClass`,
  `DType::getCardinalityClass`, `DTypeConstructor::computeCardinalityInfo`),
  without finite model finding;
- constructor, selector and tester terms (`getInstCons`, `mkTester`,
  `mkSplit`), with shared selectors off (safe mode with proofs);
- the clash of two constructor terms (`checkClash`).

Codatatypes and sygus datatypes are outside safe mode, so recursive singletons
(a property of codatatypes) never arise.
-/

namespace Telos.Solver.DT

/-- `CardinalityClass`, in cvc5's order. -/
inductive CardClass where
  | one
  | interpretedOne
  | finite
  | interpretedFinite
  | infinite
  deriving DecidableEq, Inhabited, Repr

def CardClass.rank : CardClass → Nat
  | .one => 0
  | .interpretedOne => 1
  | .finite => 2
  | .interpretedFinite => 3
  | .infinite => 4

/-- `maxCardinalityClass`. -/
def CardClass.max (a b : CardClass) : CardClass :=
  if (a == .interpretedOne && b == .finite) || (a == .finite && b == .interpretedOne) then
    .interpretedFinite
  else if a.rank ≥ b.rank then a else b

/-- `isCardinalityClassFinite` without finite model finding. -/
def CardClass.isFinite (c : CardClass) : Bool := c == .one || c == .finite

mutual
  /-- `TypeNode::getCardinalityClass`. The datatypes being computed (`busy`)
  count as infinite, as cvc5's cache has them while it computes them. -/
  partial def cardClass (busy : List TypeNode) (T : TypeNode) : CardClass :=
    match T with
    | .sort _ => .interpretedOne
    | .boolean | .bitVector _ => .finite
    | .datatype .. =>
      if busy.contains T then .infinite else
      match T.dtConstructors? with
      | some cs =>
        let base : CardClass := if cs.length == 1 then .one else .finite
        (List.range cs.length).foldl (fun c i => c.max (consInfo (T :: busy) T i).1) base
      | none => .infinite
    | .array i e =>
      let r := cardClass busy e
      if r == .finite || r == .interpretedFinite then r.max (cardClass busy i) else r
    | .set e =>
      match cardClass busy e with
      | .one => .finite
      | c => c
    | .function _ _ =>
      let r := cardClass busy T.getRangeType
      if r == .finite || r == .interpretedFinite then
        T.getArgTypes.foldl (fun c a => c.max (cardClass busy a)) r
      else r
    | _ => .infinite

  /-- `DTypeConstructor::computeCardinalityInfo`: the cardinality class of
  constructor `i` of `T`, and whether it has an argument that is (interpreted)
  finite and not a datatype. -/
  partial def consInfo (busy : List TypeNode) (T : TypeNode) (i : Nat) : CardClass × Bool :=
    let fields := (T.dtFields? i).getD []
    fields.foldl (fun (c, ext) tc =>
      let cc := cardClass busy tc
      (c.max cc, ext || (cc != .infinite && !tc.isDatatype))) (.one, false)
end

/-- `Env::isFiniteType`, without finite model finding. -/
def isFiniteType (T : TypeNode) : Bool := (cardClass [] T).isFinite

/-- `DTypeConstructor::getCardinalityClass`. -/
def consCardClass (T : TypeNode) (i : Nat) : CardClass := (consInfo [T] T i).1

/-- `DTypeConstructor::hasFiniteExternalArgType`. -/
def hasFiniteExternalArgType (T : TypeNode) (i : Nat) : Bool := (consInfo [T] T i).2

def numConstructors (T : TypeNode) : Nat := (T.dtConstructors?.map List.length).getD 0

def numFields (T : TypeNode) (i : Nat) : Nat := ((T.dtFields? i).map List.length).getD 0

/-! ## Terms -/

/-- The constructor `i` of `T` applied to `args` (`mkApplyCons`). -/
def mkCons (T : TypeNode) (i : Nat) (args : Array Node) : Node :=
  .app (.node .APPLY_CONSTRUCTOR (.const (.dtCons T i))) args

/-- Selector `j` of constructor `i` of `T`, applied to `n`. -/
def mkSel (T : TypeNode) (i j : Nat) (n : Node) : Node :=
  .app (.node .APPLY_SELECTOR (.const (.dtSel T i j))) #[n]

/-- The tester of constructor `i` of `T`, applied to `n` (`mkTester`). -/
def mkTester (n : Node) (T : TypeNode) (i : Nat) : Node :=
  .app (.node .APPLY_TESTER (.const (.dtCons T i))) #[n]

/-- `getInstCons`: constructor `i` applied to the selectors of `n`. -/
def getInstCons (n : Node) (T : TypeNode) (i : Nat) : Node :=
  mkCons T i ((Array.range (numFields T i)).map fun j => mkSel T i j n)

/-- `mkSplit`: the disjunction of the testers of `n`. -/
def mkSplit (n : Node) (T : TypeNode) : Node :=
  let ts := (Array.range (numConstructors T)).map (mkTester n T)
  if ts.size == 1 then ts[0]! else .app (.kind .OR) ts

/-- The tester index and argument of a tester application (`isTester`). -/
def isTester? : Node → Option (Nat × Node)
  | .app (.node .APPLY_TESTER (.const (.dtCons _ i))) #[a] => some (i, a)
  | _ => none

/-- A constructor application: its type, index and arguments. -/
def consApp? : Node → Option (TypeNode × Nat × Array Node)
  | .app (.node .APPLY_CONSTRUCTOR (.const (.dtCons T i))) cs => some (T, i, cs)
  | _ => none

/-- A selector application: its type, constructor and field indices, and
argument. -/
def selApp? : Node → Option (TypeNode × Nat × Nat × Node)
  | .app (.node .APPLY_SELECTOR (.const (.dtSel T i j))) #[a] => some (T, i, j, a)
  | _ => none

/-- The datatype type of a term, if it has one. -/
def dtType? (n : Node) : Option TypeNode :=
  match n.typeHint with
  | some T@(.datatype ..) => some T
  | _ => none

/-- `checkClash` (with `checkNdtConst`): whether two terms are distinct for any
value of their variables, because of their constructors or their constants of
other types. -/
partial def checkClash (a b : Node) : Bool :=
  match consApp? a, consApp? b with
  | some (T, i, as), some (U, j, bs) =>
    if i != j || T != U then true
    else (List.range as.size).any fun k => checkClash as[k]! bs[k]!
  | _, _ => a != b && a.isConst && b.isConst

end Telos.Solver.DT
