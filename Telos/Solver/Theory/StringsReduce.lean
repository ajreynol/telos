import Telos.Solver.Theory.Strings

/-!
# The reductions of the extended string functions

A port of cvc5's `StringsPreprocess::reduce`, for the functions whose reduction
has no quantified formula (`str.substr`, `str.update`, `str.indexof`,
`str.replace`), and of `utils::eagerReduce` for `str.contains`.

Each is made twice, from one definition: as cvc5's solver does, the arguments
and terms of the skolems rewritten (`SkolemCache` with a rewriter), for the
lemma sent; and without rewriting, as CPC's `string_reduction` and
`string_eager_reduction` state it, for the lemma's certificate
(`Telos/Solver/StringsLemma.lean`).
-/

namespace Telos.Solver.Strings

/-- What a reduction needs to make a skolem: the rewrite of a term (the
identity for CPC's form), and the purification skolem of a term. -/
structure SkolemOps (m : Type → Type) where
  rw : Node → m Node
  /-- The purification skolem of a (rewritten) term. -/
  purify : Node → m Node

section
variable {m : Type → Type} [Monad m] (ops : SkolemOps m)

namespace Reduce

def substr (t i l : Node) : Node := Node.mkNode .STRING_SUBSTR #[t, i, l]
def sub (a b : Node) : Node := Node.mkNode .SUB #[a, b]
def add (a b : Node) : Node := Node.mkNode .ADD #[a, b]
def concat (cs : Array Node) : Node := Node.mkNode .STRING_CONCAT cs
def contains (x y : Node) : Node := Node.mkNode .STRING_CONTAINS #[x, y]
def and (cs : Array Node) : Node := Node.mkNode .AND cs
def ite (c t e : Node) : Node := Node.mkNode .ITE #[c, t, e]

/-- A skolem of a term other than for its purification: the term itself if it
rewrites to a constant. -/
def skolem (t : Node) : m Node := do
  let t ← ops.rw t
  if t.isConst then return t
  ops.purify t

/-- `SK_PREFIX(x, n)`. -/
def prefix_ (x n : Node) : m Node := do
  let x ← ops.rw x
  skolem ops (substr x (intConst 0) (← ops.rw n))

/-- `SK_SUFFIX_REM(x, n)`. -/
def suffixRem (x n : Node) : m Node := do
  let x ← ops.rw x
  let n ← ops.rw n
  skolem ops (substr x n (sub (mkLen x) n))

/-- `SK_FIRST_CTN_PRE(x, y)` and `SK_FIRST_CTN_POST(x, y)`. -/
def firstCtn (x y : Node) : m (Node × Node) := do
  let x ← ops.rw x
  let y ← ops.rw y
  let pre ← prefix_ ops x (Node.mkNode .STRING_INDEXOF #[x, y, intConst 0])
  let post ← suffixRem ops x (add (mkLen pre) (mkLen y))
  return (pre, post)

/-- `(not (str.contains (str.++ pre (str.substr y 0 (- (str.len y) 1))) y))`:
`pre` ends before the first occurrence of `y`. -/
def firstOccurrence (pre y : Node) : Node :=
  Node.notNode (contains (concat #[pre, substr y (intConst 0) (sub (mkLen y) (intConst 1))]) y)

end Reduce

open Reduce

/-- `SK_PURIFY(t)`. -/
def purifySkolem (t : Node) : m Node := do ops.purify (← ops.rw t)

/-- `StringsPreprocess::simplify`: the reduction of an extended term `t`, with
its equality with its purification skolem last. -/
def reduceExtf (t : Node) : m (Option Node) := do
  let zero := intConst 0
  let conclude (red k : Node) : Option Node := some (Reduce.and #[red, Node.eqNode t k])
  match t with
  | .app (.kind .STRING_SUBSTR) #[s, n, l] =>
    let k ← purifySkolem ops t
    let e := add n l
    let k1 ← prefix_ ops s n
    let k2 ← suffixRem ops s e
    let cond := Reduce.and #[Node.mkNode .GEQ #[n, zero], Node.mkNode .GT #[mkLen s, n], Node.mkNode .GT #[l, zero]]
    let body := Reduce.and #[Node.eqNode s (concat #[k1, k, k2]), Node.eqNode (mkLen k1) n,
      Node.mkNode .OR #[Node.eqNode (mkLen k2) (sub (mkLen s) e), Node.eqNode (mkLen k2) zero],
      Node.mkNode .LEQ #[mkLen k, l]]
    return conclude (ite cond body (Node.eqNode k emptyWord)) k
  | .app (.kind .STRING_UPDATE) #[s, n, r] =>
    let k ← purifySkolem ops t
    let rs := match r with
      | .const (.string [_]) => r
      | _ => substr r zero (sub (mkLen s) n)
    let k1 ← prefix_ ops s n
    let k2 ← suffixRem ops s (add n (mkLen rs))
    let k3 ← purifySkolem ops (substr s n (mkLen rs))
    let cond := Reduce.and #[Node.mkNode .GEQ #[n, zero], Node.mkNode .GT #[mkLen s, n]]
    let body := Reduce.and #[Node.eqNode k (concat #[k1, rs, k2]), Node.eqNode s (concat #[k1, k3, k2]),
      Node.eqNode (mkLen k1) n, Node.eqNode (mkLen rs) (mkLen k3)]
    return conclude (ite cond body (Node.eqNode k s)) k
  | .app (.kind .STRING_INDEXOF) #[x, y, n] =>
    let k ← purifySkolem ops t
    let xn := substr x n (sub (mkLen x) n)
    let (k1, k2) ← firstCtn ops xn y
    let cond := Node.mkNode .OR #[Node.notNode (contains xn y), Node.mkNode .GT #[n, mkLen x],
      Node.mkNode .GT #[zero, n]]
    let body := Reduce.and #[Node.eqNode xn (concat #[k1, y, k2]), firstOccurrence k1 y,
      Node.eqNode k (add n (mkLen k1))]
    return conclude (ite cond (Node.eqNode k (intConst (-1)))
      (ite (Node.eqNode y emptyWord) (Node.eqNode k n) body)) k
  | .app (.kind .STRING_REPLACE) #[x, y, z] =>
    let (k1, k2) ← firstCtn ops x y
    let k ← purifySkolem ops t
    let body := Reduce.and #[Node.eqNode x (concat #[k1, y, k2]), Node.eqNode k (concat #[k1, z, k2]),
      firstOccurrence k1 y]
    return conclude (ite (Node.eqNode y emptyWord) (Node.eqNode k (concat #[z, x]))
      (ite (contains x y) body (Node.eqNode k x))) k
  | _ => return none

/-- `(= x (str.++ pre y post))` for `(str.contains x y)`
(`utils::eagerReduce`). -/
def reduceContainsPos (x y : Node) : m Node := do
  let (k1, k2) ← firstCtn ops x y
  return Node.eqNode x (concat #[k1, y, k2])

end

/-- The operations of CPC's form: no rewriting. -/
def cpcSkolems : SkolemOps Id := { rw := fun t => t, purify := fun t => Node.mkPurifySkolem t }

/-- CPC's reduction of `t` (`string_reduction`). -/
def reduceExtfCpc (t : Node) : Option Node := Id.run (reduceExtf cpcSkolems t)

/-- CPC's eager reduction of `(str.contains x y)`. -/
def eagerContainsCpc (x y : Node) : Node :=
  Node.mkNode .ITE #[Node.mkNode .STRING_CONTAINS #[x, y],
    Id.run (reduceContainsPos cpcSkolems x y), Node.notNode (Node.eqNode x y)]

end Telos.Solver.Strings
