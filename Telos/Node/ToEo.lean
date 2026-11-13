import Telos.Node.Node
import Cpc.SmtTranslate
import Cpc.SmtTyping
import Cpc.Logos

/-!
# Translation to Logos terms

`Node.toEo` gives every node its meaning: the SMT-LIB semantics of a node is the
Logos semantics of its translation (`eo_satisfiability`, through `__eo_to_smt`).
This file is therefore part of the **specification** and is listed in
`TRUSTED.md`. Keep it a direct, structural transcription of how cvc5 prints a node
in CPC, so it is easy to audit.

The encoding follows the CPC signature (`Cpc.eo`) as Ethos elaborates it:

* `and`/`or` are `:right-assoc-nil` with nil `true`/`false`, so
  `(and a b c)` is `(and a (and b (and c true)))`.
* `=`, `=>`, `xor`, `not` and `ite` have the fixed arities of cvc5's kinds.
* Indexed operators become Logos's `UOp1`/`UOp2` with numeral indices:
  `((_ extract i j) x)` is `Term.Apply (Term.UOp2 UserOp2.extract i j) x`.
* `(f a b)` is the curried `((f a) b)`, and `(-> A B C)` is `(-> A (-> B C))`.
* `(forall ((x T) …) F)` is `(forall (@list x …) F)`, where the bound variables are
  `Term.Var`s, exactly like free constants. Instantiation patterns are dropped.

A node with the wrong number of children or indices translates to `Term.Stuck`,
which has no SMT type, so it is not `WellTyped`.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- `(op x)` -/
def eoApp1 (op : UserOp) (x : Term) : Term :=
  Term.Apply (Term.UOp op) x

/-- `(op x y)` -/
def eoApp2 (op : UserOp) (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) x) y

/-- `(op x₁ (op x₂ … (op xₙ nil)))`: a `:right-assoc-nil` application. -/
def eoRightAssocNil (op : UserOp) (nil : Term) : List Term → Term
  | [] => nil
  | x :: xs => eoApp2 op x (eoRightAssocNil op nil xs)

/-- An Eunoia list `(@list x₁ … xₙ)`, as used for binder variable lists. -/
def eoList : List Term → Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoList xs)

namespace TypeNode

def toEo : TypeNode → Term
  | .boolean => Term.Bool
  | .integer => Term.UOp UserOp.Int
  | .real => Term.UOp UserOp.Real
  | .string => Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  | .regExp => Term.UOp UserOp.RegLan
  | .bitVector w => Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)
  | .array i e => Term.Apply (Term.Apply (Term.UOp UserOp.Array) i.toEo) e.toEo
  | .sequence e => Term.Apply (Term.UOp UserOp.Seq) e.toEo
  | .set e => Term.Apply (Term.UOp UserOp.Set) e.toEo
  | .function a r => Term.Apply (Term.Apply Term.FunType a.toEo) r.toEo
  | .sort id => Term.USort id

end TypeNode

namespace Const

def toEo : Const → Term
  | .boolean b => Term.Boolean b
  | .integer n => Term.Numeral n
  | .rational q => Term.Rational q
  | .bitVector w v => Term.Binary w v
  | .string s => Term.String s

end Const

/-- How many children an application takes. -/
inductive Arity where
  | exactly (n : Nat)
  | atLeast (n : Nat)
  deriving DecidableEq, Repr

def Arity.accepts : Arity → Nat → Bool
  | .exactly n, m => m == n
  | .atLeast n, m => n ≤ m

/-- The nil terminator of a `:right-assoc-nil` operator. -/
inductive Nil where
  /-- The same nil for every type, like `true` for `and`. -/
  | const (t : Term)
  /-- `(eo::nil op (eo::typeof x₁))`, computed from the first element, like `0`
  or `0/1` for `+`. -/
  | typed

/-- The nil of a `:right-assoc-nil` operator whose nil depends on the type of
its elements: `(eo::nil op (eo::typeof x₁))`. -/
def typedNil (op : UserOp) (x : Term) : Term :=
  __eo_nil (Term.UOp op) (__eo_typeof x)

/-- The nil of `op` for a list whose first element is `x`. -/
def Nil.eval (op : UserOp) : Nil → Term → Term
  | .const t, _ => t
  | .typed, x => typedNil op x

/-- How an application is written in CPC. Every operator is described by one of
these shapes, so the translation (and its congruence proof) is uniform. -/
inductive AppShape where
  /-- `(head x₁ … xₙ)`, curried: `Apply (… (Apply head x₁) …) xₙ`. -/
  | spine (head : Term) (arity : Arity)
  /-- A `:right-assoc-nil` operator: `(op x₁ (op x₂ … (op xₙ nil)))`, n ≥ 2. The
  nil terminator is computed from the first element `x₁`, as Logos's parser and
  Eunoia do (`Nil.eval`). -/
  | rightAssocNil (op : UserOp) (nil : Nil)
  /-- A binder variable list `(@list x₁ … xₙ)`. -/
  | binderList
  /-- A binder `(op vars body)`, with optional instantiation patterns (dropped). -/
  | binder (op : UserOp)
  /-- No CPC counterpart; translates to `Term.Stuck`. -/
  | none

/-- The CPC form of each operator kind. This table is the heart of the
specification for operator kinds; keep it in line with `Cpc.eo`. -/
def Kind.eoShape : Kind → AppShape
  | .EQUAL => .spine (Term.UOp UserOp.eq) (.exactly 2)
  | .NOT => .spine (Term.UOp UserOp.not) (.exactly 1)
  | .AND => .rightAssocNil UserOp.and (.const (Term.Boolean true))
  | .OR => .rightAssocNil UserOp.or (.const (Term.Boolean false))
  | .IMPLIES => .spine (Term.UOp UserOp.imp) (.exactly 2)
  | .XOR => .spine (Term.UOp UserOp.xor) (.exactly 2)
  | .ITE => .spine (Term.UOp UserOp.ite) (.exactly 3)
  | .ADD => .rightAssocNil UserOp.plus .typed
  | .MULT => .rightAssocNil UserOp.mult .typed
  | .SUB => .spine (Term.UOp UserOp.neg) (.exactly 2)
  | .NEG => .spine (Term.UOp UserOp.__eoo_neg_2) (.exactly 1)
  | .DIVISION => .spine (Term.UOp UserOp.qdiv) (.exactly 2)
  | .INTS_DIVISION => .spine (Term.UOp UserOp.div) (.exactly 2)
  | .INTS_MODULUS => .spine (Term.UOp UserOp.mod) (.exactly 2)
  | .DIVISION_TOTAL => .spine (Term.UOp UserOp.qdiv_total) (.exactly 2)
  | .INTS_DIVISION_TOTAL => .spine (Term.UOp UserOp.div_total) (.exactly 2)
  | .INTS_MODULUS_TOTAL => .spine (Term.UOp UserOp.mod_total) (.exactly 2)
  | .ABS => .spine (Term.UOp UserOp.abs) (.exactly 1)
  | .LT => .spine (Term.UOp UserOp.lt) (.exactly 2)
  | .LEQ => .spine (Term.UOp UserOp.leq) (.exactly 2)
  | .GT => .spine (Term.UOp UserOp.gt) (.exactly 2)
  | .GEQ => .spine (Term.UOp UserOp.geq) (.exactly 2)
  | .TO_REAL => .spine (Term.UOp UserOp.to_real) (.exactly 1)
  | .TO_INTEGER => .spine (Term.UOp UserOp.to_int) (.exactly 1)
  | .IS_INTEGER => .spine (Term.UOp UserOp.is_int) (.exactly 1)
  | .BOUND_VAR_LIST => .binderList
  | .FORALL => .binder UserOp.forall
  | .EXISTS => .binder UserOp.exists
  | _ => .none

/-- The CPC form of each indexed operator. -/
def indexedEoShape : Kind → List Int → AppShape
  | .BITVECTOR_EXTRACT, [i, j] =>
      .spine (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) (.exactly 1)
  | _, _ => .none

/-- The CPC form of an operator that is a term, given its translation `f`. -/
def nodeEoShape : Kind → Term → AppShape
  | .APPLY_UF, f => .spine f (.atLeast 1)
  | _, _ => .none

/-- Shapes whose congruence is proven child by child: rewriting any child to an
equivalent node gives an equivalent application. Binders are handled separately,
since their variable list is not a term. -/
def AppShape.isChildCongruent : AppShape → Bool
  | .spine _ _ => true
  | .rightAssocNil op (.const _) => op == UserOp.and || op == UserOp.or
  | .rightAssocNil op .typed => op == UserOp.plus || op == UserOp.mult
  | .none => true
  | .binderList | .binder _ => false

/-- Translate an application of the given shape to its translated children. -/
def AppShape.toEo : AppShape → List Term → Term
  | .spine head arity, xs => if arity.accepts xs.length then xs.foldl Term.Apply head else Term.Stuck
  | .rightAssocNil op nil, xs =>
    if 2 ≤ xs.length then eoRightAssocNil op (nil.eval op (xs.headD Term.Stuck)) xs
    else Term.Stuck
  | .binderList, xs => eoList xs
  | .binder op, [vs, body] | .binder op, [vs, body, _] => eoApp2 op vs body
  | .binder _, _ => Term.Stuck
  | .none, _ => Term.Stuck

namespace Node

def toEo : Node → Term
  | .const c => c.toEo
  | .var name T => Term.Var (Term.String (native_string_lit name)) T.toEo
  | .boundVar name T => Term.Var (Term.String (native_string_lit name)) T.toEo
  | .app (.kind k) cs => k.eoShape.toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)
  | .app (.indexed k is) cs =>
      (indexedEoShape k is.toList).toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)
  | .app (.node k f) cs =>
      (nodeEoShape k f.toEo).toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)

/-- The CPC shape of an application with operator `op`. -/
def _root_.Telos.Op.eoShape : Op → AppShape
  | .kind k => k.eoShape
  | .indexed k is => indexedEoShape k is.toList
  | .node k f => nodeEoShape k f.toEo

theorem toEo_app (op : Op) (cs : Array Node) :
    (Node.app op cs).toEo = op.eoShape.toEo (cs.toList.map Node.toEo) := by
  cases op <;> (rw [Node.toEo]; simp [Op.eoShape])

/-- The Logos SMT term of a node. -/
def toSmt (t : Node) : SmtTerm :=
  __eo_to_smt t.toEo

/-- The Logos SMT type of a node; `SmtType.None` when it is ill typed. -/
def smtType (t : Node) : SmtType :=
  __smtx_typeof t.toSmt

/-- A node is well typed when its translation has an SMT type. -/
def WellTyped (t : Node) : Prop :=
  t.smtType ≠ SmtType.None

instance (t : Node) : Decidable t.WellTyped :=
  inferInstanceAs (Decidable (_ ≠ _))

end Node

/-- The CPC formula `(= t s)`. -/
def eqFormula (t s : Node) : Term :=
  eoApp2 UserOp.eq t.toEo s.toEo

namespace TypeNode

/-- The type of a Logos SMT type, if `TypeNode` has one for it. -/
def ofSmt : SmtType → Option TypeNode
  | .Bool => some .boolean
  | .Int => some .integer
  | .Real => some .real
  | .RegLan => some .regExp
  | .BitVec w => some (.bitVector w)
  | .Seq .Char => some .string
  | .Seq e => .sequence <$> ofSmt e
  | .Set e => .set <$> ofSmt e
  | .Map i e => .array <$> ofSmt i <*> ofSmt e
  | .FunType a r => .function <$> ofSmt a <*> ofSmt r
  | .USort i => some (.sort i)
  | _ => none

end TypeNode

namespace Node

/-- cvc5's `getType()`: the type of a well-typed node, and `none` for an
ill-typed one. It is computed by Logos's type checker, so there is no second
type system to keep in sync. -/
def getType (t : Node) : Option TypeNode :=
  TypeNode.ofSmt t.smtType

theorem wellTyped_of_getType {t : Node} {T : TypeNode} (h : t.getType = some T) :
    t.WellTyped := by
  intro hNone
  simp [getType, hNone, TypeNode.ofSmt] at h

end Node

end Telos
