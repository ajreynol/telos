import Std.Data.HashMap
import Telos.Core.Node.Key
import Telos.Core.Node.Order

/-!
# cvc5's order of node ids, approximated

cvc5 orders some things by node id: the monomials of a sum
(`LeafNodeComparator`), the sides of an equality, the disjuncts of some lemmas.
A node's id is its creation order (`NodeManager`, hash-consed: a node built
again keeps its id). The structural order `Node.lt` cannot reproduce it: cvc5
puts `(g z z)` before `(f w)` when the input mentions it first.

`NodeOrder` approximates the ids as cvc5's parser creates them: the declared
constants in their order of declaration, then the terms of the input
assertions in the order of their first occurrence, children before parents and
left to right. A term not in the table was created later, by preprocessing or
solving: it comes after the terms of the table, and two such terms are compared
by `Node.lt`.

Untrusted: like `Node.lt`, the order only decides which normal form telos
builds, and every normal form is certified whatever the order.
-/

namespace Telos

/-- cvc5's node ids, approximated (see the module docstring). The empty order
is `Node.lt`. -/
structure NodeOrder where
  /-- The declared constants, by name, in order of declaration. -/
  decl : Std.HashMap String Nat := {}
  /-- The other terms of the input, in order of first occurrence. -/
  ids : Std.HashMap Key Nat := {}
  deriving Inhabited

instance : Repr NodeOrder := ⟨fun o _ => s!"<NodeOrder: {o.decl.size} declared, {o.ids.size} terms>"⟩

namespace NodeOrder

/-- The approximate id of `t`, if it is in the table. -/
def id? (o : NodeOrder) (t : Node) : Option Nat :=
  match t with
  | .var name _ => match o.decl.get? name with
    | some i => some i
    | none => (o.ids.get? ⟨t⟩).map (· + o.decl.size)
  | _ => (o.ids.get? ⟨t⟩).map (· + o.decl.size)

/-- `a` has a smaller id than `b` (cvc5: `a.getId() < b.getId()`). -/
def lt (o : NodeOrder) (a b : Node) : Bool :=
  if o.decl.isEmpty && o.ids.isEmpty then Node.lt a b else
  match o.id? a, o.id? b with
  | some i, some j => i < j
  | some _, none => true
  | none, some _ => false
  | none, none => Node.lt a b

/-- Number the subterms of `t` not numbered yet, children first, left to right
(the order in which cvc5's parser creates them). -/
partial def visit (ids : Std.HashMap Key Nat) (t : Node) : Std.HashMap Key Nat :=
  if ids.contains ⟨t⟩ then ids else
  let ids := match t with
    | .app op cs =>
      let ids := match op with
        | .node _ f => visit ids f
        | _ => ids
      cs.foldl visit ids
    | .skolem _ cs => cs.foldl visit ids
    | _ => ids
  ids.insert ⟨t⟩ ids.size

/-- The order of an input: the declared constants `decls`, in order, and the
assertions `as`, in order. -/
def ofInput (decls : List String) (as : List Node) : NodeOrder :=
  { decl := decls.zipIdx.foldl (fun m (x, i) => if m.contains x then m else m.insert x i) {},
    ids := as.foldl visit {} }

end NodeOrder

end Telos
