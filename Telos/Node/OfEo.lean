import Telos.Node.ToEo

/-!
# From Logos terms back to nodes

`Node.ofEo` is a partial inverse of `Node.toEo`. It reads the right-hand side of a
CPC rule's conclusion back as a node.

It is **not** part of the specification and needs no proof. Every use is checked:
a rewrite step only accepts `m := ofEo r` after checking that `m.toEo = r`
(`Telos/Rewriter/Certified.lean`). So a gap here (a term it cannot read back)
only means that a rewrite does not apply.

Variables are read back as the matching variable of the node being rewritten,
when there is one, which keeps bound variables bound. Otherwise they become free
variables.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

namespace TypeNode

/-- The inverse of `TypeNode.toEo`. -/
def ofEo : Term → Option TypeNode
  | .Bool => some .boolean
  | .UOp UserOp.Int => some .integer
  | .UOp UserOp.Real => some .real
  | .UOp UserOp.RegLan => some .regExp
  | .Apply (.UOp UserOp.Seq) (.UOp UserOp.Char) => some .string
  | .Apply (.UOp UserOp.BitVec) (.Numeral w) => some (.bitVector w)
  | .Apply (.Apply (.UOp UserOp.Array) i) e => .array <$> ofEo i <*> ofEo e
  | .Apply (.UOp UserOp.Seq) e => .sequence <$> ofEo e
  | .Apply (.UOp UserOp.Set) e => .set <$> ofEo e
  | .Apply (.Apply .FunType a) r => .function <$> ofEo a <*> ofEo r
  | .USort i => some (.sort i)
  | _ => none

end TypeNode

namespace Const

/-- The inverse of `Const.toEo`. -/
def ofEo : Term → Option Const
  | .Boolean b => some (.boolean b)
  | .Numeral n => some (.integer n)
  | .Rational q => some (.rational q)
  | .Binary w v => some (.bitVector w v)
  | .String s => some (.string s)
  | _ => none

end Const

/-- The head and arguments of an application spine `(… ((h x₁) x₂) … xₙ)`. -/
def eoSpine : Term → Term × List Term
  | .Apply f x => let (h, xs) := eoSpine f; (h, xs ++ [x])
  | t => (t, [])

/-- The elements of `(op x₁ (op x₂ … (op xₙ nil)))`. -/
def eoRightAssocNilElems (op : UserOp) (nil : Term) : Term → Option (List Term)
  | .Apply (.Apply (.UOp o) x) rest =>
      if o == op then (x :: ·) <$> eoRightAssocNilElems op nil rest else none
  | t => if t == nil then some [] else none

/-- The elements of an Eunoia list `(@list x₁ … xₙ)`. -/
def eoListElems : Term → Option (List Term)
  | .Apply (.Apply .__eo_List_cons x) rest => (x :: ·) <$> eoListElems rest
  | .__eo_List_nil => some []
  | _ => none

/-- A string literal of Logos, as a Lean string. -/
def nativeStringToString (s : native_String) : String :=
  String.ofList (s.map Char.ofNat)

namespace Node

/-- The variables (free and bound) occurring in a node. -/
partial def vars : Node → List Node
  | n@(.var ..) | n@(.boundVar ..) => [n]
  | .const _ => []
  | .app op cs =>
      let opVars := match op with
        | .node _ f => f.vars
        | _ => []
      opVars ++ cs.toList.flatMap vars

/-- The node a Logos variable stands for: the variable of `env` with this
translation, or a free variable. -/
def varOfEo (env : List Node) (t : Term) (bound : Bool) : Option Node :=
  match env.find? (·.toEo == t) with
  | some v => some v
  | none =>
    match t with
    | .Var (.String s) T =>
      (if bound then Node.boundVar else Node.var) (nativeStringToString s) <$> TypeNode.ofEo T
    | _ => none

/-- A partial inverse of `toEo`, for the kinds `toEo` translates. Variables are
looked up in `env` first (see the module doc). -/
partial def ofEo (env : List Node) (t : Term) : Option Node := do
  if let some c := Const.ofEo t then return .const c
  if let .Var .. := t then return ← varOfEo env t false
  let (h, xs) := eoSpine t
  match h, xs with
  | .UOp UserOp.and, [_, _] => nary .AND UserOp.and (Term.Boolean true)
  | .UOp UserOp.or, [_, _] => nary .OR UserOp.or (Term.Boolean false)
  | .UOp UserOp.eq, [_, _] => app .EQUAL xs
  | .UOp UserOp.not, [_] => app .NOT xs
  | .UOp UserOp.imp, [_, _] => app .IMPLIES xs
  | .UOp UserOp.xor, [_, _] => app .XOR xs
  | .UOp UserOp.ite, [_, _, _] => app .ITE xs
  | .UOp UserOp.forall, [vs, body] => binder .FORALL vs body
  | .UOp UserOp.exists, [vs, body] => binder .EXISTS vs body
  | .UOp2 UserOp2.extract (.Numeral i) (.Numeral j), [x] =>
      return .app (.indexed .BITVECTOR_EXTRACT #[i, j]) #[← ofEo env x]
  | f@(.Var ..), _ :: _ =>
      return .app (.node .APPLY_UF (← varOfEo env f false)) (← xs.mapM (ofEo env)).toArray
  | _, _ => none
where
  app (k : Kind) (xs : List Term) : Option Node := do
    return .app (.kind k) (← xs.mapM (ofEo env)).toArray
  nary (k : Kind) (op : UserOp) (nil : Term) : Option Node := do
    let elems ← eoRightAssocNilElems op nil t
    if elems.length < 2 then none
    app k elems
  binder (k : Kind) (vs body : Term) : Option Node := do
    let bvs ← (← eoListElems vs).mapM (varOfEo env · true)
    return .app (.kind k) #[.app (.kind .BOUND_VAR_LIST) bvs.toArray, ← ofEo env body]

end Node

end Telos
