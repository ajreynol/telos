import Std.Data.HashMap
import Telos.Core.Node.Key
import Telos.Core.Node.Order
import Telos.Core.Node.FastType

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
  /-- The other terms: of the input, in order of first occurrence, then those
  numbered after (`add`). -/
  ids : Std.HashMap Key Nat := {}
  /-- The number of terms of the input (the first ids). -/
  inputSize : Nat := 0
  /-- Terms created after all those of `ids`, numbered after them (`withLocal`):
  a small table, so that extending the order does not copy `ids`. -/
  fresh : Std.HashMap Key Nat := {}
  deriving Inhabited

instance : Repr NodeOrder := ⟨fun o _ => s!"<NodeOrder: {o.decl.size} declared, {o.ids.size} terms>"⟩

namespace NodeOrder

/-- Whether `t` has an integral real constant (`cvx` changes it). -/
partial def hasIntegralRat : Node → Bool
  | .const (.rational q) => q.den == 1
  | .app _ cs => cs.any hasIntegralRat
  | _ => false

/-- The node cvc5's rewriter builds for the rewritten node `t`: its arithmetic
is mixed, so an integral constant of a real term is an integer (`(>= s 2)`,
where the parser's `(>= s 2.0)` is another node). -/
partial def cvx (t : Node) : Node :=
  match t with
  | .const (.rational q) => if q.den == 1 then .const (.integer q.num) else t
  | .app op cs => if hasIntegralRat t then .app op (cs.map cvx) else t
  | t => t

/-- Whether the arithmetic rewriter builds nodes of `t`'s shape: an arithmetic
relation, its negation, or an arithmetic term (decided by the operator, not
the type, to be cheap; not, say, a conjunction a pass built). -/
def rewriterShape : Node → Bool
  | .app (.kind k) cs =>
    k == .GEQ || k == .GT || k == .LEQ || k == .LT || k == .ADD || k == .MULT ||
      k == .NEG || k == .SUB || k == .TO_REAL || k == .DIVISION ||
      (k == .NOT && cs.size == 1 && match cs[0]! with
        | .app (.kind k') _ => k' == .GEQ || k' == .EQUAL
        | _ => false) ||
      (k == .EQUAL && cs.any fun c => match c with
        | .const (.rational _) => true
        | .app (.kind k') _ => k' == .ADD || k' == .MULT || k' == .TO_REAL
        | _ => false)
  | .const (.rational _) => true
  | _ => false

/-- `acc` with `cvx t` when the rewriter builds `t` and it has an integral
real constant (otherwise `cvx t` is `t`, already in `acc`). -/
def pushCvx (acc : Array Node) (t : Node) : Array Node :=
  if rewriterShape t && hasIntegralRat t then acc.push (cvx t) else acc

/-- The approximate id of `t`, if it is in the table: of the node cvc5's
rewriter builds for it (`cvx`; a node with an integral real constant is not a
pass's node of the same shape), or else, for a term of the input, its own
(the rewrite of an unchanged input atom has no node in a certificate). -/
def id? (o : NodeOrder) (t : Node) : Option Nat :=
  match t with
  | .var name _ => match o.decl.get? name with
    | some i => some i
    | none => (o.ids.get? ⟨t⟩).map (· + o.decl.size)
  | _ =>
    let r := if hasIntegralRat t then
        (o.ids.get? ⟨cvx t⟩) <|> ((o.ids.get? ⟨t⟩).filter (· < o.inputSize))
      else o.ids.get? ⟨t⟩
    match r with
    | some i => some (i + o.decl.size)
    | none => (o.fresh.get? ⟨t⟩).map (· + o.decl.size + o.ids.size)

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

/-- Number `t`'s subterms not numbered yet (`visit`), as a node created after
the ones numbered (by preprocessing, which creates its subterms first). -/
def add (o : NodeOrder) (t : Node) : NodeOrder := { o with ids := visit o.ids t }

/-- Number the subterms of `t` that `o` does not number, after all of its own,
in `fresh` (which this replaces): a term built (a lemma, before its rewrite)
after the nodes `o` numbers. An empty order stays empty (`Node.lt`). -/
partial def withLocal (o : NodeOrder) (t : Node) : NodeOrder :=
  if o.decl.isEmpty && o.ids.isEmpty then o else
  let rec go (m : Std.HashMap Key Nat) (t : Node) : Std.HashMap Key Nat :=
    if m.contains ⟨t⟩ || (o.ids.contains ⟨t⟩) then m else
    let m := match t with
      | .app op cs =>
        let m := match op with
          | .node _ f => go m f
          | _ => m
        cs.foldl go m
      | .skolem _ cs => cs.foldl go m
      | _ => m
    match t with
    | .var name _ => if o.decl.contains name then m else m.insert ⟨t⟩ m.size
    | _ => m.insert ⟨t⟩ m.size
  { o with fresh := go {} t }

/-- The order of an input: the declared constants `decls`, in order, and the
assertions `as`, in order. -/
def ofInput (decls : List String) (as : List Node) : NodeOrder :=
  let ids := as.foldl visit {}
  { decl := decls.zipIdx.foldl (fun m (x, i) => if m.contains x then m else m.insert x i) {},
    ids := ids, inputSize := ids.size }

end NodeOrder

end Telos
