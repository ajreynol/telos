import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Preprocess.Pipeline
import Telos.Preprocess.ConjProof
import Telos.Preprocess.Options
import Telos.Core.PolyNorm
import Telos.Rewriter.Rewrite

/-!
# The `static-learning` pass

cvc5's `StaticLearning` pass (`src/preprocessing/passes/static_learning.cpp`):
each assertion not seen before is split into its conjuncts (nested `and`s), and
each conjunct is given to the theories' `ppStaticLearn`, in the order of the
theories, which learn lemmas implied by it; the lemmas are added after the last
assertion, rewritten.

Ported learners:

* UF's diamonds (`DiamondsProofGenerator::ppStaticLearn`): for
  `(or (and (= a b) (= b d)) (and (= a f) (= f d)))`, up to the orientation of
  the equalities, the lemma `(=> n (= a d))`;
* arithmetic's (`ArithStaticLearner`, with `--arith-static-learning`), below
  each conjunct, children first: for an `ite` whose condition compares its
  branches (`(ite (>= t e) t e)`, `iteMinMax`), the lemmas that it is at least
  (or at most) both; and for an `ite` whose branches have lower (upper) bounds,
  the lemma that it has the least (greatest) of them (`iteConstant`), under the
  bounds of the branches that are not constants. The bounds are those of
  numerals, of earlier `ite`s, and the lower bounds `(>= x c)` that arithmetic's
  `ppAssert` saw in non-clausal simplification (`ArithStaticLearner::addBound`).
  They last for the whole run, as cvc5's.

Not ported: bit-vectors' (a lemma for sums of two powers of two, which cvc5 adds
without a proof).

cvc5 adds these lemmas as trusted steps (`ARITH_STATIC_LEARN`, `DIAMONDS`).
telos proves each in CPC (`iteLemma`, `diamondLemma`), and skips a lemma it
cannot prove.
-/

namespace Telos.Preprocess

open Eo Node Proof

/-- The state of the pass, and of cvc5's `ArithStaticLearner`. -/
structure SLState where
  /-- `d_minMap`: lower bounds. -/
  minMap : Std.HashMap Key Rat := {}
  /-- `d_maxMap`: upper bounds. -/
  maxMap : Std.HashMap Key Rat := {}
  /-- `StaticLearning::d_cache`: the nodes split so far. -/
  cache : Std.HashSet Key := {}
  /-- The lemmas, in order. -/
  lemmas : Array Node := #[]

/-- The value of a numeral. -/
def numeralValue? : Node → Option Rat
  | .const (.integer n) => some n
  | .const (.rational q) => some q
  | _ => none

/-- `ArithStaticLearner::addBound` of a literal `ppAssert` saw: `(>= x c)` for a
variable `x` is a lower bound, kept if it is tighter. (The other relations do
not occur on rewritten literals.) -/
def SLState.addBound (s : SLState) (l : Node) : SLState :=
  match l with
  | .app (.kind .GEQ) #[x, c] =>
    match x, numeralValue? c with
    | .var .., some v =>
      match s.minMap.get? ⟨x⟩ with
      | some w => if w < v then { s with minMap := s.minMap.insert ⟨x⟩ v } else s
      | none => { s with minMap := s.minMap.insert ⟨x⟩ v }
    | _, _ => s
  | _ => s

/-- `expr::hasBoundVar`: `n` has a bound variable. -/
def hasBoundVar (n : Node) : Bool := Id.run do
  let mut stack := #[n]
  let mut seen : Std.HashSet Key := {}
  for _ in [0:1000000] do
    let some m := stack.back? | return false
    stack := stack.pop
    if seen.contains ⟨m⟩ then continue
    seen := seen.insert ⟨m⟩
    match m with
    | .boundVar .. => return true
    | .app _ cs => stack := stack ++ cs
    | _ => pure ()
  return false

/-- A numeral of the type of `n` (an integer or a real). -/
def numeralLike (n : Node) (q : Rat) : Node := Arith.constNode (Arith.isReal n) q

/-- `oldSimplifiedKind` of a relation, and `reverseRelationKind`. -/
def reverseRel : Kind → Kind
  | .LT => .GT
  | .LEQ => .GEQ
  | .GEQ => .LEQ
  | .GT => .LT
  | k => k

/-- `ArithStaticLearner::iteMinMax`. -/
def iteMinMax (n : Node) : List Node :=
  match n with
  | .app (.kind .ITE) #[c, t₀, e₀] =>
    match c with
    | .app (.kind k₀) #[cl, cr] =>
      if !(k₀ == .LT || k₀ == .LEQ || k₀ == .GT || k₀ == .GEQ) then [] else
      let (t, e, k) := if t₀ == cr && e₀ == cl then (e₀, t₀, reverseRel k₀) else (t₀, e₀, k₀)
      if t == cl && e == cr then
        match k with
        | .LT | .LEQ => [mkNode .LEQ #[n, t], mkNode .LEQ #[n, e]]
        | _ => [mkNode .GEQ #[n, t], mkNode .GEQ #[n, e]]
      else []
    | _ => []
  | _ => []

/-- `ArithStaticLearner::iteConstant`: the lemmas, and the new bounds of `n`. -/
def iteConstant (s : SLState) (n : Node) : SLState :=
  match n with
  | .app (.kind .ITE) #[_, a, b] =>
    let s := match s.minMap.get? ⟨a⟩, s.minMap.get? ⟨b⟩ with
      | some va, some vb =>
        let m := min va vb
        if (s.minMap.get? ⟨n⟩).all (· < m) then
          let conc := mkNode .GEQ #[n, numeralLike n m]
          let conj := (if a.isConst then [] else [mkNode .GEQ #[a, numeralLike n va]]) ++
            (if b.isConst then [] else [mkNode .GEQ #[b, numeralLike n vb]])
          let lem := match conj with
            | [] => conc
            | [x] => mkNode .IMPLIES #[x, conc]
            | xs => mkNode .IMPLIES #[mkNode .AND xs.toArray, conc]
          { s with minMap := s.minMap.insert ⟨n⟩ m, lemmas := s.lemmas.push lem }
        else s
      | _, _ => s
    match s.maxMap.get? ⟨a⟩, s.maxMap.get? ⟨b⟩ with
    | some va, some vb =>
      let m := max va vb
      if (s.maxMap.get? ⟨n⟩).all (m < ·) then
        let conc := mkNode .LEQ #[n, numeralLike n m]
        let conj := (if a.isConst then [] else [mkNode .LEQ #[a, numeralLike n va]]) ++
          (if b.isConst then [] else [mkNode .LEQ #[b, numeralLike n vb]])
        let lem := match conj with
          | [] => conc
          | [x] => mkNode .IMPLIES #[x, conc]
          | xs => mkNode .IMPLIES #[mkNode .AND xs.toArray, conc]
        { s with maxMap := s.maxMap.insert ⟨n⟩ m, lemmas := s.lemmas.push lem }
      else s
    | _, _ => s
  | _ => s

/-- `ArithStaticLearner::process`. -/
def arithProcess (s : SLState) (n : Node) : SLState :=
  match n with
  | .app (.kind .ITE) #[c, a, b] =>
    if hasBoundVar n then s else
    let s := if c.getKind != .EQUAL then { s with lemmas := s.lemmas ++ (iteMinMax n).toArray } else s
    if (s.minMap.contains ⟨a⟩ && s.minMap.contains ⟨b⟩) ||
        (s.maxMap.contains ⟨a⟩ && s.maxMap.contains ⟨b⟩) then iteConstant s n
    else s
  | .const (.integer _) | .const (.rational _) =>
    match numeralValue? n with
    | some v => { s with minMap := s.minMap.insert ⟨n⟩ v, maxMap := s.maxMap.insert ⟨n⟩ v }
    | none => s
  | _ => s

/-- A traversal of `n`, children first, as cvc5's static learners do it (a stack
of nodes, a node processed once its children are). `enter` tells whether to
visit the children of a node. -/
def postOrder (n : Node) (enter : Node → Bool) : Array Node := Id.run do
  let mut work := #[n]
  let mut processed : Std.HashSet Key := {}
  let mut out := #[]
  for _ in [0:10000000] do
    let some m := work.back? | break
    let kids := if enter m then m.getChildren else #[]
    let mut unprocessed := false
    for c in kids do
      if !processed.contains ⟨c⟩ then
        work := work.push c
        unprocessed := true
    if unprocessed then continue
    work := work.pop
    if processed.contains ⟨m⟩ then continue
    processed := processed.insert ⟨m⟩
    out := out.push m
  return out

/-- `ArithStaticLearner::staticLearning`. -/
def arithStaticLearning (s : SLState) (n : Node) : SLState :=
  (postOrder n fun _ => true).foldl arithProcess s

/-- `DiamondsProofGenerator::ppStaticLearn`, on one node. -/
def diamond? (n : Node) : Option Node := do
  let .app (.kind .OR) #[.app (.kind .AND) #[.app (.kind .EQUAL) #[a, b], .app (.kind .EQUAL) #[c, d]],
      .app (.kind .AND) #[.app (.kind .EQUAL) #[e, f], .app (.kind .EQUAL) #[g, h]]] := n | none
  let (a, d) ←
    if a == c then some (b, d) else if a == d then some (b, c)
    else if b == c then some (a, d) else if b == d then some (a, c) else none
  let (e, h) ←
    if e == g then some (f, h) else if e == h then some (f, g)
    else if f == g then some (e, h) else if f == h then some (e, g) else none
  if (a == e && d == h) || (a == h && d == e) then
    some (mkNode .IMPLIES #[n, eqNode a d])
  else none

/-- UF's static learning: the diamonds below `n`, children first (not below
binders). -/
def ufStaticLearning (s : SLState) (n : Node) : SLState :=
  (postOrder n fun m => !m.getKind.isQuantifier).foldl (init := s) fun s m =>
    match diamond? m with
    | some l => { s with lemmas := s.lemmas.push l }
    | none => s

/-- `StaticLearning::flattenAnd`: the conjuncts of `n` not seen before. -/
def SLState.flattenAnd (s : SLState) (n : Node) : SLState × Array Node := Id.run do
  let mut visit := #[n]
  let mut cache := s.cache
  let mut out := #[]
  for _ in [0:10000000] do
    let some cur := visit.back? | break
    visit := visit.pop
    if cache.contains ⟨cur⟩ then continue
    cache := cache.insert ⟨cur⟩
    if cur.getKind == .AND then visit := visit ++ cur.getChildren
    else out := out.push cur
  return ({ s with cache }, out)

/-! ## Proofs of the lemmas -/

/-- `(r X Y)` from the fact `f` of `(r X₀ Y₀)`, with `X₀ - Y₀ = X - Y`. -/
def normRelE (f : Nat) (from_ to_ : Node) : EmitM Nat := do
  match from_.getChildren, to_.getChildren with
  | #[x₀, y₀], #[x, y] =>
    let real := Arith.isReal x
    let pn ← stepE .arith_poly_norm
      [(Arith.scaledEq real 1 1 (mkNode .SUB #[x₀, y₀]) (mkNode .SUB #[x, y])).toEo] []
    let e ← stepE .arith_poly_norm_rel [(eqNode from_ to_).toEo] [pn]
    stepE .eq_resolve [] [f, e]
  | _, _ => throw "normRel"

/-- A true relation between numerals, by `evaluate`. -/
def numeralFactE (r : Node) : EmitM Nat := do
  let e ← stepE .evaluate [r.toEo] []
  stepE .true_elim [] [e]

/-- `(>= b m)` from the fact `f` of `(>= b k)`, `k ≥ m` (`geq`), or `(<= b m)`
from `(<= b k)`, `k ≤ m`: by `arith_sum_ub` with `(<= m k)` (or `(<= k m)`). -/
def weakenE (geq : Bool) (f : Nat) (b k m : Node) : EmitM Nat := do
  if geq then
    -- `(<= k b)`, then `(<= m b)` by transitivity, then `(>= b m)`
    let e ← stepE .arith_elim_leq [k.toEo, b.toEo] []
    let e ← stepE .symm [] [e]
    let f' ← stepE .eq_resolve [] [f, e]
    let z ← numeralFactE (mkNode .LEQ #[m, k])
    let s ← stepE .arith_sum_ub [] [z, f']
    let le ← normRelE s (mkNode .LEQ #[mkNode .ADD #[m, k], mkNode .ADD #[k, b]]) (mkNode .LEQ #[m, b])
    let e ← stepE .arith_elim_leq [m.toEo, b.toEo] []
    stepE .eq_resolve [] [le, e]
  else
    let z ← numeralFactE (mkNode .LEQ #[k, m])
    let s ← stepE .arith_sum_ub [] [f, z]
    normRelE s (mkNode .LEQ #[mkNode .ADD #[b, k], mkNode .ADD #[k, m]]) (mkNode .LEQ #[b, m])

/-- `(= L true)` for an `iteMinMax` lemma `L`, by cvc5's rules:
`(>= (ite (>= a b) a b) K)` for `K` `a` or `b` is `arith-max-geq1`/`2`; and
`(<= (ite (>= b a) a b) K)`, whose `ite` is `(ite (< b a) b a)` (`ite-not-cond`,
`arith-elim-lt`), is `arith-min-lt1`/`2`. -/
def minMaxE (L : Node) : EmitM Nat := do
  let .app (.kind rel) #[n, K] := L | throw "minmax shape"
  let .app (.kind .ITE) #[C, a, b] := n | throw "minmax shape"
  let .app (.kind .GEQ) #[ca, cb] := C | throw "minmax condition"
  if rel == .GEQ && ca == a && cb == b then
    if K == a then return ← stepE .arith_max_geq1 [a.toEo, b.toEo] []
    if K == b then return ← stepE .arith_max_geq2 [a.toEo, b.toEo] []
  if rel == .LEQ && ca == b && cb == a then
    -- `n = (ite (not (>= b a)) b a) = (ite (< b a) b a)`
    let flipped := iteNode (notNode C) b a
    let e₁ ← stepE .ite_not_cond [C.toEo, b.toEo, a.toEo] []
    let e₁ ← stepE .symm [] [e₁]
    let el ← stepE .arith_elim_lt [b.toEo, a.toEo] []
    let el ← stepE .symm [] [el]
    let ra ← closeChain a #[]
    let rb ← closeChain b #[]
    let e₂ ← congStep flipped (.kind .ITE) [el, rb, ra]
    let rk ← closeChain K #[]
    let e₃ ← congStep L (.kind rel) [← stepE .trans [] [e₁, e₂], rk]
    let rule ← if K == b then pure CRule.arith_min_lt1
      else if K == a then pure CRule.arith_min_lt2 else throw "minmax bound"
    let e₄ ← stepE rule [b.toEo, a.toEo] []
    return ← stepE .trans [] [e₃, e₄]
  throw "minmax: no rule"

/-- The proof of an arithmetic static learning lemma `L`: `(r (ite C s t) K)`,
or `(=> A (r (ite C s t) K))`, for `r` `>=` or `<=`. Assuming `A`, the relation
is lifted into the `ite` (`arith-geq-ite-lift`, `arith-leq-ite-lift`), each
branch that `A` bounds is `true` (by the bound, weakened if it is tighter), and
the rewriter takes the rest to `true` (numerals, and `iteMinMax`'s branches). -/
def iteLemmaE (L : Node) : EmitM Nat := do
  let (ante, conc) := match L with
    | .app (.kind .IMPLIES) #[a, c] => (some a, c)
    | c => (none, c)
  let .app (.kind rel) #[n, K] := conc | throw "lemma shape"
  let .app (.kind .ITE) #[C, s, t] := n | throw "lemma shape"
  let geq ← match rel with
    | .GEQ => pure true
    | .LEQ => pure false
    | _ => throw "lemma relation"
  let B₁ := mkNode rel #[s, K]
  let B₂ := mkNode rel #[t, K]
  if ante.isNone && (rewriteCert (iteNode C B₁ B₂)).1 != mkTrue then
    -- an `iteMinMax` lemma the rewriter does not close
    return ← stepE .true_elim [] [← minMaxE conc]
  let facts ← match ante with
    | some a => do conjunctsE (← assumeE a) a
    | none => pure []
  let e₁ ← stepE (if geq then .arith_geq_ite_lift else .arith_leq_ite_lift)
    [C.toEo, s.toEo, t.toEo, K.toEo] []
  -- the branches
  let branch (b : Node) : EmitM (Option Nat) := do
    let B := mkNode rel #[b, K]
    if let some (_, p) := facts.find? (·.1 == B) then
      return some (← stepE .true_intro [] [p])
    let bound := facts.find? fun (F, _) => match F with
      | .app (.kind r') #[b', k'] => r' == rel && b' == b && k'.isConst
      | _ => false
    match bound with
    | some (.app _ #[_, k], p) =>
      let w ← weakenE geq p b k K
      return some (← stepE .true_intro [] [w])
    | _ => return none
  let q₁ ← branch s
  let q₂ ← branch t
  let lifted := iteNode C B₁ B₂
  let mid := iteNode C (if q₁.isSome then mkTrue else B₁) (if q₂.isSome then mkTrue else B₂)
  let chain ← if q₁.isNone && q₂.isNone then pure [e₁] else do
    let rc ← closeChain C #[]
    let r₁ ← match q₁ with | some q => pure q | none => closeChain B₁ #[]
    let r₂ ← match q₂ with | some q => pure q | none => closeChain B₂ #[]
    pure [e₁, ← congStep lifted (.kind .ITE) [rc, r₁, r₂]]
  let r := rewriteCert mid
  if r.1 != mkTrue then throw "lemma: not rewritten to true"
  let chain := match ← rwFact r with
    | some f => chain ++ [f]
    | none => chain
  let eq ← closeChain conc chain.toArray
  let c ← stepE .true_elim [] [eq]
  if ante.isSome then scopeE c else pure c

/-- `(= a d)` from the facts `(= x₁ y₁)` and `(= x₂ y₂)`, by `symm` and
`trans`. -/
def eqChainE (a d : Node) (e₁ e₂ : Node × Nat) : EmitM Nat := do
  if a == d then return ← closeChain a #[]
  let oriented (e : Node × Nat) : EmitM (List (Node × Node × Nat)) := do
    match e.1 with
    | .app (.kind .EQUAL) #[x, y] => return [(x, y, e.2), (y, x, ← stepE .symm [] [e.2])]
    | _ => throw "diamond"
  let o₁ ← oriented e₁
  let o₂ ← oriented e₂
  for (u, v, p) in o₁ ++ o₂ do
    for (u', v', p') in o₁ ++ o₂ do
      if p != p' && u == a && v == u' && v' == d then
        return ← stepE .trans [] [p, p']
  throw "diamond: no chain"

/-- The proof of a diamond lemma `(=> (or D₁ D₂) (= a d))`: each `Dᵢ`, a
conjunction of two equalities, gives `(= a d)` by transitivity, so
`(=> Dᵢ (= a d))` (`scope`); with the disjunction, resolution gives
`(= a d)`. -/
def diamondLemmaE (L : Node) : EmitM Nat := do
  let .app (.kind .IMPLIES) #[n, g] := L | throw "diamond shape"
  let .app (.kind .OR) #[D₁, D₂] := n | throw "diamond shape"
  let .app (.kind .EQUAL) #[a, d] := g | throw "diamond shape"
  let pn ← assumeE n
  let impl (D : Node) : EmitM Nat := do
    let pd ← assumeE D
    let cs ← conjunctsE pd D
    let some e₁ := cs[0]? | throw "diamond"
    let some e₂ := cs[1]? | throw "diamond"
    scopeE (← eqChainE a d e₁ e₂)
  let i₁ ← impl D₁
  let i₂ ← impl D₂
  let c₁ ← stepE .implies_elim [] [i₁]
  let c₂ ← stepE .implies_elim [] [i₂]
  -- `(or D₁ D₂)`, `(or (not D₁) g)`: `(or D₂ g)`; with `(or (not D₂) g)`: `g`
  let r₁ ← stepE .resolution [.Boolean true, D₁.toEo] [pn, c₁]
  let r₂ ← stepE .resolution [.Boolean true, D₂.toEo] [r₁, c₂]
  let f ← stepE .factoring [] [r₂]
  scopeE f

/-- A lemma as a certified rewrite of `true`, from its proof, then rewritten
(cvc5 adds static learning lemmas rewritten). -/
def lemmaOf (L : Node) (prf : EmitM Nat) (o : NodeOrder := {}) : Option (Rw mkTrue) := do
  let r ← runE mkTrue (do
    let p ← prf
    let e ← stepE .true_intro [] [p]
    stepE .symm [] [e])
  if r.1 != L then none
  return r.trans (rewriteCert r.1 o)

/-- The `static-learning` pass, with the bounds that non-clausal simplification's
`ppAssert` saw. -/
def Pipeline.staticLearning {input : Node} (p : Pipeline input) (opts : PPOptions)
    (bounds : Array Node) (o : NodeOrder := {}) : Pipeline input :=
  if Pipeline.inConflict p then p
  else
    let s₀ : SLState := bounds.foldl SLState.addBound {}
    let s := (Pipeline.assertions p).foldl (init := s₀) fun s a =>
      if s.cache.contains ⟨a⟩ then s
      else
        let (s, conjs) := s.flattenAnd a
        conjs.foldl (init := s) fun s c =>
          let s := ufStaticLearning s c
          if opts.arithStaticLearning then arithStaticLearning s c else s
    let lems := s.lemmas.toList.filterMap fun L =>
      let prf := if L.getKind == .IMPLIES && (L.getChildren[0]?.map (·.getKind == .OR)).getD false
        then diamondLemmaE L else iteLemmaE L
      match lemmaOf L prf o with
      | some r => some r
      | none => Profile.time "static-learning" (fun _ => s!"unproven: {L.toSmtLib}") fun _ => none
    Pipeline.pushLemmas p (lems.flatMap splitLemma)

end Telos.Preprocess
