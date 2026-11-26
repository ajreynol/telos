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
  /-- The nullary constructors, as terms, with the place of their names in the
  declarations: cvc5's parser creates their terms with their datatypes. -/
  declNodes : Std.HashMap Key Nat := {}
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

/-- Whether `op` applies a term (an uninterpreted function, a constructor...),
whose arguments have the types of its signature: a real argument stays a real
constant (`(u 1.0)`). -/
def appliesTerm : Op → Bool
  | .node _ _ => true
  | _ => false

/-- The node cvc5's rewriter builds for the rewritten node `t`: its arithmetic
is mixed, so an integral constant of a real term is an integer (`(>= s 2)`,
where the parser's `(>= s 2.0)` is another node). Not a constant argument of
a function (`appliesTerm`), only the arithmetic of its other arguments. -/
partial def cvx (t : Node) : Node :=
  match t with
  | .const (.rational q) => if q.den == 1 then .const (.integer q.num) else t
  | .app op cs =>
    if !hasIntegralRat t then t
    else if appliesTerm op then .app op (cs.map fun c => if c.isConst then c else cvx c)
    else .app op (cs.map cvx)
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

/-- Whether `t` is a product of non-constants, which cvc5's rewriter builds as
a `NONLINEAR_MULT`: another node than the input's `MULT` of the same factors,
created when the rewriter first builds it. -/
def isProduct : Node → Bool
  | .app (.kind .MULT) cs => cs.size ≥ 2 && cs.all (!·.isConst)
  | _ => false

/-- A node no term has, which marks the keys of `nlKey`. -/
def nlTag : Node := .boundVar "@nonlinear_mult" .boolean

/-- The key under which the table numbers the `NONLINEAR_MULT` of the product
`t`: its factors in a fixed order (that of `Node.lt`, so that the products of
the same factors in any order share it), marked by `nlTag`. -/
def nlKey (t : Node) : Node :=
  .app (.kind .MULT) ((t.getChildren.toList.mergeSort fun a b => !Node.lt b a).toArray.push nlTag)

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
    if let some i := o.declNodes.get? ⟨t⟩ then some i else
    -- a product: of its `NONLINEAR_MULT`, if the rewriter has built it,
    -- otherwise of the input's `MULT`
    let nl : Option Nat := if isProduct t then
        let k := nlKey t
        match o.ids.get? ⟨k⟩ with
        | some i => some (i + o.decl.size)
        | none => (o.fresh.get? ⟨k⟩).map (· + o.decl.size + o.ids.size)
      else none
    if nl.isSome then nl else
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

/-- `lt`, without the ids of the terms created during solving (`fresh`), which
change as more are created: for an order that must not change during solving,
as that of the factors of a product, whose node would otherwise change. -/
def ltStable (o : NodeOrder) (a b : Node) : Bool := lt { o with fresh := {} } a b

/-- `ids` with the `NONLINEAR_MULT` of `t` numbered, if `t` is a product whose
one is not numbered yet (`nlKey`). -/
def numberNl (ids : Std.HashMap Key Nat) (t : Node) (other : Std.HashMap Key Nat := {}) :
    Std.HashMap Key Nat :=
  if !isProduct t then ids else
  let k := nlKey t
  if ids.contains ⟨k⟩ || other.contains ⟨k⟩ then ids else ids.insert ⟨k⟩ ids.size

/-- Number the subterms of `t` not numbered yet, children first, left to right
(the order in which cvc5's parser creates them). With `nl`, of nodes cvc5's
rewriter built, also the `NONLINEAR_MULT` of their products (`numberNl`),
which the parser's `MULT`s are not. -/
partial def visit (ids : Std.HashMap Key Nat) (t : Node) (nl : Bool := false) : Std.HashMap Key Nat :=
  if ids.contains ⟨t⟩ then (if nl then numberNl ids t else ids) else
  let ids := match t with
    | .app op cs =>
      let ids := match op with
        | .node _ f => visit ids f nl
        | _ => ids
      cs.foldl (visit · · nl) ids
    | .skolem _ cs => cs.foldl (visit · · nl) ids
    | _ => ids
  let ids := ids.insert ⟨t⟩ ids.size
  if nl then numberNl ids t else ids

/-- Number `t`'s subterms not numbered yet (`visit`), as a node created after
the ones numbered (by preprocessing, which creates its subterms first). -/
def add (o : NodeOrder) (t : Node) : NodeOrder := { o with ids := visit o.ids t true }

/-- `fresh` with the subterms of `t` that neither `o` nor `fresh` numbers, after
them: the nodes of a term built during solving (a lemma, before its rewrite),
created after all the others, children first, as cvc5's node ids are. -/
partial def numberFresh (o : NodeOrder) (fresh : Std.HashMap Key Nat) (t : Node) : Std.HashMap Key Nat :=
  if o.decl.isEmpty && o.ids.isEmpty then fresh else
  let rec go (m : Std.HashMap Key Nat) (t : Node) : Std.HashMap Key Nat :=
    if m.contains ⟨t⟩ || (o.ids.contains ⟨t⟩) then numberNl m t o.ids else
    let m := match t with
      | .app op cs =>
        let m := match op with
          | .node _ f => go m f
          | _ => m
        cs.foldl go m
      | .skolem _ cs => cs.foldl go m
      | _ => m
    let m := match t with
      | .var name _ => if o.decl.contains name then m else m.insert ⟨t⟩ m.size
      | _ => m.insert ⟨t⟩ m.size
    numberNl m t o.ids
  go fresh t

/-- The nodes cvc5's arithmetic rewriter creates on the way to the rewrite of
`t`, in order: for `(> a c)` (`c` an integer), `(<= a c)`, `(not (<= a c))`,
then, rewriting the former, `(>= a c+1)` and `(not (>= a c+1))`. -/
partial def rewriteIntermediates (acc : Array Node) (t : Node) : Array Node :=
  match t with
  | .app (.kind k) cs =>
    let acc := cs.foldl rewriteIntermediates acc
    match k, cs with
    | .GT, #[a, .const (.integer c)] =>
      let le := Node.app (.kind .LEQ) #[a, .const (.integer c)]
      let ge := Node.app (.kind .GEQ) #[a, .const (.integer (c + 1))]
      acc ++ #[le, .app (.kind .NOT) #[le], ge, .app (.kind .NOT) #[ge]]
    | _, _ => acc
  | _ => acc

/-- `numberFresh` of `t`, then of the nodes its rewrite creates
(`rewriteIntermediates`). -/
def numberFreshRewrite (o : NodeOrder) (fresh : Std.HashMap Key Nat) (t : Node) : Std.HashMap Key Nat :=
  (rewriteIntermediates #[] t).foldl o.numberFresh (o.numberFresh fresh t)

/-- The order with the subterms of `t` that it does not number yet numbered
after the others (`numberFresh`), as nodes a rewrite creates: children first,
left to right. -/
def extend (o : NodeOrder) (t : Node) : NodeOrder := { o with fresh := o.numberFresh o.fresh t }

/-- The order with the subterms of `t` numbered after its own (`numberFresh`
from none). -/
def withLocal (o : NodeOrder) (t : Node) : NodeOrder := { o with fresh := o.numberFresh {} t }

/-- The integer constants cvc5's theories create when they are built, which
it does when the first assertion is processed (after it is parsed, before the
next): `0` to `8`, as their orientation in shared equalities shows. -/
def solverConstants : List Node := (List.range 9).map fun (i : Nat) => Node.const (.integer (Int.ofNat i))

/-- The order of an input: the declared constants `decls`, in order, and the
assertions `as`, in order, with the solvers' constants (`solverConstants`)
after the first. -/
def ofInput (decls : List String) (as : List Node) (consName : Node → Option String := fun _ => none) :
    NodeOrder :=
  let ids := match as with
    | [] => {}
    | a :: rest => rest.foldl visit (solverConstants.foldl visit (visit {} a))
  let decl := decls.zipIdx.foldl (fun m (x, i) => if m.contains x then m else m.insert x i) {}
  -- the nullary constructors of the input, at their names' places
  let declNodes := ids.fold (init := {}) fun (m : Std.HashMap Key Nat) k _ =>
    match k.node with
    | .app (.node .APPLY_CONSTRUCTOR _) #[] =>
      match (consName k.node).bind decl.get? with
      | some i => m.insert k i
      | none => m
    | _ => m
  { decl, declNodes, ids := ids, inputSize := ids.size }

end NodeOrder

end Telos
