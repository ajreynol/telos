import Telos.Core.Node.Node

/-!
# A total order on nodes

cvc5 orders nodes by id, for example to orient equalities (`(= a b)` with
`a.getId() > b.getId()` becomes `(= b a)`) and to sort the children of
commutative operators. Ids depend on creation order, which telos cannot
reproduce, so it uses this fixed structural order instead: constants, then nullary
constructors, then free variables, then bound variables, then applications; within each, by payload,
name and type, or by operator and then children, lexicographically.

Untrusted: the order only decides which certified rewrite to try.
-/

namespace Telos

namespace Const

private def rank : Const → Nat
  | .boolean _ => 0
  | .integer _ => 1
  | .rational _ => 2
  | .bitVector .. => 3
  | .string _ => 4
  | .emptySet _ => 5
  | .dtCons .. => 6
  | .dtSel .. => 7

private def cmpOfLt {α} [LT α] [DecidableEq α] [DecidableLT α] (a b : α) : Ordering :=
  if a = b then .eq else if a < b then .lt else .gt

def cmp : Const → Const → Ordering
  | .boolean a, .boolean b => compare a b
  | .integer a, .integer b => compare a b
  | .rational a, .rational b => cmpOfLt a b
  | .bitVector w v, .bitVector w' v' => (compare w w').then (compare v v')
  | .string a, .string b => compare a b
  | .emptySet T, .emptySet U => compare T U
  | .dtCons T i, .dtCons U j => (compare T U).then (compare i j)
  | .dtSel T i j, .dtSel U k l => ((compare T U).then (compare i k)).then (compare j l)
  | a, b => compare a.rank b.rank

end Const

namespace Node

/-- Nullary constructors come after constants and before variables: cvc5 creates
them when their datatype is declared, so they usually have smaller ids than the
constants declared after it (`(= nil x)`). -/
private def rank : Node → Nat
  | .const _ => 0
  | .app (.node .APPLY_CONSTRUCTOR _) #[] => 1
  | .var .. => 2
  | .boundVar .. => 3
  | .skolem .. => 4
  | .app .. => 5

mutual

/-- The structural order on nodes. -/
partial def cmp : Node → Node → Ordering
  | .const a, .const b => a.cmp b
  | .var n T, .var m U | .boundVar n T, .boundVar m U => (compare n m).then (compare T U)
  | .skolem i cs, .skolem j ds => (compare i j).then (listCmp cs.toList ds.toList)
  | a@(.app op cs), b@(.app op' cs') =>
    (compare a.rank b.rank).then ((opCmp op op').then (listCmp cs.toList cs'.toList))
  | a, b => compare a.rank b.rank

partial def opCmp : Op → Op → Ordering
  | .kind k, .kind k' => compare k k'
  | .indexed k is, .indexed k' is' => (compare k k').then (compare is.toList is'.toList)
  | .node k f, .node k' f' => (compare k k').then (cmp f f')
  | .kind _, _ => .lt
  | _, .kind _ => .gt
  | .indexed .., _ => .lt
  | _, .indexed .. => .gt

partial def listCmp : List Node → List Node → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmp a b).then (listCmp as bs)

end

/-- `a` comes before `b` in the order (cvc5: `a.getId() < b.getId()`). -/
def lt (a b : Node) : Bool := cmp a b == .lt

end Node

end Telos
