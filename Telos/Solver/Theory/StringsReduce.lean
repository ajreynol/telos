import Telos.Solver.Theory.Strings

/-!
# The reductions of the extended string functions

A port of cvc5's `StringsPreprocess::reduce`, for every extended function, of `utils::eagerReduce` for `str.contains`, and of the
unfolding of a negative membership (`RegExpOpr::reduceRegExpNeg`).

Each is made twice, from one definition: as cvc5's solver does, the arguments
and terms of the skolems rewritten (`SkolemCache` with a rewriter), for the
lemma sent; and without rewriting, as CPC's `string_reduction` and
`string_eager_reduction` state it, for the lemma's certificate
(`Telos/Solver/StringsLemma.lean`).
-/

namespace Telos.Solver.Strings

/-- `SkolemCache::mkIndexVar`, `mkLengthVar`. -/
def indexVar : Node := .boundVar "@var.str_index" .integer
def lengthVar : Node := .boundVar "@var.str_length" .integer

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
  | .app (.kind .STRING_CONTAINS) #[x, s] =>
    -- (the negative one)
    let k ← purifySkolem ops t
    let i := indexVar
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LEQ #[i, sub (mkLen x) (mkLen s)]),
      Node.notNode (Node.eqNode (substr x i (mkLen s)) s)]
    return conclude (Node.eqNode k (Node.notNode (Node.mkBoundedForall #[i] body))) k
  | .app (.kind .STRING_LEQ) #[s, u] =>
    let k ← purifySkolem ops t
    let i := indexVar
    let code (x : Node) : Node := Node.mkNode .STRING_TO_CODE #[substr x i (intConst 1)]
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LEQ #[i, mkLen s]), Node.notNode (Node.mkNode .LEQ #[i, mkLen u]),
      Node.notNode (Node.eqNode (substr s zero i) (substr u zero i)),
      ite k (Node.mkNode .GEQ #[code s, code u]) (Node.mkNode .GEQ #[code u, code s])]
    return conclude (ite (Node.eqNode s u) k (Node.notNode (Node.mkBoundedForall #[i] body))) k
  | .app (.kind .STRING_REV) #[x] =>
    let k ← purifySkolem ops t
    let i := indexVar
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LT #[i, mkLen k]),
      Node.eqNode (substr k i (intConst 1))
        (substr x (sub (mkLen x) (add i (intConst 1))) (intConst 1))]
    return conclude (Reduce.and #[Node.eqNode (mkLen x) (mkLen k), Node.mkBoundedForall #[i] body]) k
  | .app (.kind .STRING_ITOS) #[n] =>
    let k ← purifySkolem ops t
    let u (a : Node) : Node := Node.applyUF (.skolem .STRINGS_ITOS_RESULT #[n]) #[a]
    let one := intConst 1
    let i := indexVar
    let c := sub (Node.mkNode .STRING_TO_CODE #[substr k i one]) (intConst 48)
    let u1 := u (add i one)
    let digit := Reduce.and #[Node.mkNode .GEQ #[c,
        ite (Reduce.and #[Node.eqNode i zero, Node.mkNode .GT #[mkLen k, one]]) one zero],
      Node.mkNode .LT #[c, intConst 10]]
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LT #[i, mkLen k]),
      Reduce.and #[Node.eqNode u1 (add c (Node.mkNode .MULT #[intConst 10, u i])), digit,
        Node.mkNode .GEQ #[n, u1]]]
    return conclude (ite (Node.mkNode .GEQ #[n, zero])
      (Reduce.and #[Node.mkNode .GEQ #[mkLen k, one], Node.eqNode n (u (mkLen k)), Node.eqNode zero (u zero),
        Node.mkBoundedForall #[i] body])
      (Node.eqNode k emptyWord)) k
  | .app (.kind .STRING_STOI) #[s] =>
    let k ← purifySkolem ops t
    let u (a : Node) : Node := Node.applyUF (.skolem .STRINGS_STOI_RESULT #[s]) #[a]
    let nd := Node.skolem .STRINGS_STOI_NON_DIGIT #[s]
    let one := intConst 1
    let ten := intConst 10
    let i := indexVar
    let code (j : Node) : Node := sub (Node.mkNode .STRING_TO_CODE #[substr s j one]) (intConst 48)
    let ndc := code nd
    let notDigits := Reduce.and #[Node.eqNode k (intConst (-1)),
      Node.mkNode .OR #[Node.eqNode s emptyWord, Reduce.and #[Node.mkNode .GEQ #[nd, zero],
        Node.mkNode .LT #[nd, mkLen s], Node.mkNode .OR #[Node.mkNode .LT #[ndc, zero], Node.mkNode .GEQ #[ndc, ten]]]]]
    let c := code i
    let u1 := u (add i one)
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LT #[i, mkLen s]),
      Reduce.and #[Node.eqNode u1 (add c (Node.mkNode .MULT #[ten, u i])),
        Reduce.and #[Node.mkNode .GEQ #[c, zero], Node.mkNode .LT #[c, ten]], Node.mkNode .GEQ #[k, u1]]]
    return conclude (ite (Node.mkNode .LT #[k, zero]) notDigits
      (Reduce.and #[Node.eqNode k (u (mkLen s)), Node.eqNode zero (u zero), Node.mkNode .GT #[mkLen s, zero],
        Node.mkBoundedForall #[i] body])) k
  | .app (.kind .STRING_REPLACE_ALL) #[x, y, z] =>
    let k ← purifySkolem ops t
    let num := Node.skolem .STRINGS_NUM_OCCUR #[x, y]
    let us (a : Node) : Node := Node.applyUF (.skolem .STRINGS_REPLACE_ALL_RESULT #[x, y, z]) #[a]
    let uf (a : Node) : Node := Node.applyUF (.skolem .STRINGS_OCCUR_INDEX #[x, y]) #[a]
    let idx (a : Node) : Node := Node.mkNode .STRING_INDEXOF #[x, y, a]
    let i := indexVar
    let i1 := add i (intConst 1)
    let ii := idx (uf i)
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LT #[i, num]),
      Reduce.and #[Node.notNode (Node.eqNode ii (intConst (-1))),
        Node.eqNode (us i) (concat #[substr x (uf i) (sub ii (uf i)), z, us i1]),
        Node.eqNode (uf i1) (add ii (mkLen y))]]
    return conclude (ite (Node.eqNode y emptyWord) (Node.eqNode k x)
      (Reduce.and #[Node.mkNode .GEQ #[num, zero], Node.eqNode k (us zero),
        Node.eqNode (us num) (substr x (uf num) (mkLen x)), Node.eqNode (uf zero) zero,
        Node.eqNode (idx (uf num)) (intConst (-1)), Node.mkBoundedForall #[i] body])) k
  | .app (.kind .STRING_REPLACE_RE) #[x, r, z] =>
    let k ← purifySkolem ops t
    let idx := Node.mkNode .STRING_INDEXOF_RE #[x, r, zero]
    -- the first match (`RE_FIRST_MATCH_PRE`, `RE_FIRST_MATCH`, `RE_FIRST_MATCH_POST`)
    -- (CPC's, of terms not rewritten, unlike cvc5's solver: the second is in the
    -- quantified formula, under which the certificate does not relate skolems)
    let occ1 := Node.applyUF (.skolem .STRINGS_OCCUR_INDEX_RE #[x, r]) #[intConst 1]
    let k1 ← ops.purify (substr x zero idx)
    let k2 ← ops.purify (substr x idx (sub occ1 idx))
    let k3 ← ops.purify (substr x occ1 (sub (mkLen x) occ1))
    let l := lengthVar
    let shortest := Node.mkBoundedForall #[l] (Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[l, zero]),
      Node.notNode (Node.mkNode .LT #[l, mkLen k2]),
      Node.notNode (Node.mkNode .STRING_IN_REGEXP #[substr k2 zero l, r])])
    return conclude (ite (Node.mkNode .STRING_IN_REGEXP #[emptyWord, r]) (Node.eqNode k (concat #[z, x]))
      (ite (Node.eqNode idx (intConst (-1))) (Node.eqNode k x)
        (Reduce.and #[Node.eqNode x (concat #[k1, k2, k3]), Node.eqNode (mkLen k1) idx, shortest,
          Node.mkNode .STRING_IN_REGEXP #[k2, r], Node.eqNode k (concat #[k1, z, k3])]))) k
  | .app (.kind .STRING_REPLACE_RE_ALL) #[x, r, z] =>
    let k ← purifySkolem ops t
    let num := Node.skolem .STRINGS_NUM_OCCUR_RE #[x, r]
    let us (a : Node) : Node := Node.applyUF (.skolem .STRINGS_REPLACE_RE_ALL_RESULT #[x, r, z]) #[a]
    let uf (a : Node) : Node := Node.applyUF (.skolem .STRINGS_OCCUR_INDEX_RE #[x, r]) #[a]
    let rp := Node.mkNode .REGEXP_DIFF #[r, Node.mkNode .STRING_TO_REGEXP #[emptyWord]]
    let idx (w a : Node) : Node := Node.mkNode .STRING_INDEXOF_RE #[w, rp, a]
    let neg := intConst (-1)
    let rest := substr x (uf num) (mkLen x)
    let i := indexVar
    let l := lengthVar
    let i1 := add i (intConst 1)
    let ii := idx x (uf i)
    let len1 := sub (uf i1) ii
    let shortest := Node.mkBoundedForall #[l] (Node.mkNode .OR #[Node.notNode (Node.mkNode .GT #[l, zero]),
      Node.notNode (Node.mkNode .LT #[l, len1]),
      Node.notNode (Node.mkNode .STRING_IN_REGEXP #[substr x ii l, r])])
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LT #[i, num]),
      Reduce.and #[Node.mkNode .GT #[len1, zero], Node.mkNode .STRING_IN_REGEXP #[substr x ii len1, rp], shortest,
        Node.eqNode (us i) (concat #[substr x (uf i) (sub ii (uf i)), z, us i1])]]
    return conclude (ite (Node.eqNode (idx x zero) neg) (Node.eqNode k x)
      (Reduce.and #[Node.mkNode .GT #[num, zero], Node.eqNode k (us zero), Node.eqNode (us num) rest,
        Node.eqNode (uf zero) zero, Node.eqNode (idx rest zero) neg, Node.mkBoundedForall #[i] body])) k
  | .app (.kind kd) #[x] =>
    if kd != .STRING_TO_LOWER && kd != .STRING_TO_UPPER then return none
    let k ← purifySkolem ops t
    let i := indexVar
    let code (y : Node) : Node := Node.mkNode .STRING_TO_CODE #[substr y i (intConst 1)]
    let ci := code x
    let (lb, ub, off) : Int × Int × Int := if kd == .STRING_TO_UPPER then (97, 122, -32) else (65, 90, 32)
    let res := ite (Reduce.and #[Node.mkNode .LEQ #[intConst lb, ci], Node.mkNode .LEQ #[ci, intConst ub]])
      (add ci (intConst off)) ci
    let body := Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, zero]),
      Node.notNode (Node.mkNode .LT #[i, mkLen k]), Node.eqNode (code k) res]
    return conclude (Reduce.and #[Node.eqNode (mkLen x) (mkLen k), Node.mkBoundedForall #[i] body]) k
  | .app (.kind .STRING_INDEXOF_RE) #[s, r, n] =>
    let k ← purifySkolem ops t
    let i := indexVar
    let l := lengthVar
    let neg := Node.eqNode k (intConst (-1))
    let inRe (a b : Node) : Node := Node.mkNode .STRING_IN_REGEXP #[substr s a b, r]
    let first := Node.mkBoundedForall #[i, l] (Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[i, n]),
      Node.notNode (Node.mkNode .LT #[i, ite neg (mkLen s) k]), Node.notNode (Node.mkNode .GT #[l, zero]),
      Node.notNode (Node.mkNode .LEQ #[l, sub (mkLen s) i]), Node.notNode (inRe i l)])
    let here := Node.mkBoundedForall #[l] (Node.mkNode .OR #[Node.notNode (Node.mkNode .GEQ #[l, zero]),
      Node.notNode (Node.mkNode .LEQ #[l, sub (mkLen s) k]), Node.notNode (inRe k l)])
    let mtch := Node.mkNode .OR #[neg, Reduce.and #[Node.mkNode .GEQ #[k, n], Node.notNode here]]
    return conclude (ite (Node.mkNode .OR #[Node.mkNode .GT #[n, mkLen s], Node.mkNode .GT #[zero, n]]) neg
      (ite (Node.mkNode .STRING_IN_REGEXP #[emptyWord, r]) (Node.eqNode k n) (Reduce.and #[first, mtch]))) k
  | _ => return none

/-- `RegExpEntail::getFixedLengthForRegexp`. -/
partial def fixedReLength (r : Node) : Option Nat :=
  match r with
  | .app (.kind .STRING_TO_REGEXP) #[.const (.string w)] => some w.length
  | .app (.kind .REGEXP_ALLCHAR) _ | .app (.kind .REGEXP_RANGE) _ => some 1
  | .app (.kind .REGEXP_UNION) cs | .app (.kind .REGEXP_INTER) cs => do
    let ls ← cs.mapM fixedReLength
    let l ← ls[0]?
    if ls.all (· == l) then some l else none
  | .app (.kind .REGEXP_CONCAT) cs => do
    let ls ← cs.mapM fixedReLength
    return ls.foldl (· + ·) 0
  | _ => none

/-- `RegExpOpr::simplify` of a negative membership: the conclusion of its
unfolding, quantifier-free if an end of the concatenation has a fixed length,
then with whether that is the last (`none` if quantified). -/
def reduceRegExpNeg (s r : Node) : Option (Node × Option Bool) :=
  let zero := intConst 0
  let notIn (x r : Node) : Node := Node.notNode (Node.mkNode .STRING_IN_REGEXP #[x, r])
  let pre (n : Node) : Node := substr s zero n
  let suf (n : Node) : Node := substr s n (sub (mkLen s) n)
  let cat (rs : Array Node) : Node := if rs.size == 1 then rs[0]! else Node.mkNode .REGEXP_CONCAT rs
  let i := indexVar
  match r with
  | .app (.kind .REGEXP_CONCAT) rs =>
    let front := rs[0]!
    let rest := cat (rs.extract 1 rs.size)
    match fixedReLength front with
    | some n =>
      some (Node.mkNode .OR #[notIn (pre (intConst n)) front, notIn (suf (intConst n)) rest], some false)
    | none =>
      match fixedReLength rs.back! with
      | some n =>
        let n := intConst n
        some (Node.mkNode .OR #[notIn (substr s (sub (mkLen s) n) n) rs.back!,
          notIn (pre (sub (mkLen s) n)) (cat rs.pop)], some true)
      | none =>
        some (Node.mkBoundedForall #[i] (Node.mkNode .OR #[Node.mkNode .LT #[i, zero],
          Node.mkNode .LT #[mkLen s, i], notIn (pre i) front, notIn (suf i) rest]), none)
  | .app (.kind .REGEXP_STAR) #[b] =>
    some (Reduce.and #[Node.notNode (Node.eqNode s emptyWord),
      Node.mkBoundedForall #[i] (Node.mkNode .OR #[Node.mkNode .LEQ #[i, zero], Node.mkNode .LT #[mkLen s, i],
        notIn (pre i) b, notIn (suf i) r])], none)
  | _ => none

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
