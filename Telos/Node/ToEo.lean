import Telos.Node.Node
import Cpc.SmtTranslate
import Cpc.SmtTyping

/-!
# Translation to Logos terms

`Node.toEo` gives every node its meaning: the SMT-LIB semantics of a node is the
Logos semantics of its translation (`eo_satisfiability`, through `__eo_to_smt`).
This file is therefore part of the **specification** and is listed in
`TRUSTED.md`. Keep it a direct, structural transcription of how cvc5 prints a node
in CPC, so it is easy to audit.

N-ary operators follow the CPC signature (`Cpc.eo`) as Ethos elaborates it:

* `and`/`or` are `:right-assoc-nil` with nil `true`/`false`, so
  `(and a b c)` is `(and a (and b (and c true)))`.
* `=`, `=>`, `xor`, `not` and `ite` have the fixed arities of cvc5's kinds.

A node with the wrong number of children translates to `Term.Stuck`, which has no
SMT type, so it is not `WellTyped`.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

namespace TypeNode

def toEo : TypeNode → Term
  | .boolean => Term.Bool
  | .integer => Term.UOp UserOp.Int
  | .real => Term.UOp UserOp.Real
  | .bitVector w => Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)

end TypeNode

namespace Const

def toEo : Const → Term
  | .boolean b => Term.Boolean b
  | .integer n => Term.Numeral n
  | .rational q => Term.Rational q
  | .bitVector w v => Term.Binary w v

end Const

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

/-- Translate an operator application, given its translated children. -/
def appToEo : Kind → List Term → Term
  | .EQUAL, [x, y] => eoApp2 UserOp.eq x y
  | .NOT, [x] => eoApp1 UserOp.not x
  | .AND, xs@(_ :: _ :: _) => eoRightAssocNil UserOp.and (Term.Boolean true) xs
  | .OR, xs@(_ :: _ :: _) => eoRightAssocNil UserOp.or (Term.Boolean false) xs
  | .IMPLIES, [x, y] => eoApp2 UserOp.imp x y
  | .XOR, [x, y] => eoApp2 UserOp.xor x y
  | .ITE, [c, x, y] => Term.Apply (eoApp2 UserOp.ite c x) y
  | _, _ => Term.Stuck

namespace Node

def toEo : Node → Term
  | .const c => c.toEo
  | .var name T => Term.Var (Term.String (native_string_lit name)) T.toEo
  | .app k cs => appToEo k (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)

/-- The Logos SMT type of a node; `SmtType.None` when it is ill typed. -/
def smtType (t : Node) : SmtType :=
  __smtx_typeof (__eo_to_smt t.toEo)

/-- A node is well typed when its translation has an SMT type. -/
def WellTyped (t : Node) : Prop :=
  t.smtType ≠ SmtType.None

instance (t : Node) : Decidable t.WellTyped :=
  inferInstanceAs (Decidable (_ ≠ _))

end Node

end Telos
