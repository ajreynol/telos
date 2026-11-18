import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Preprocess.Pipeline
import Telos.Preprocess.Theory.ArithPreprocess
import Telos.Preprocess.Theory.BVPreprocess
import Telos.Preprocess.Theory.DatatypesPreprocess
import Telos.Preprocess.Theory.StringsPreprocess
import Telos.Rewriter.Rewrite

/-!
# The `theory-preprocess` pass

cvc5's `TheoryPreprocess` pass (`src/preprocessing/passes/theory_preprocess.cpp`)
and the `TheoryPreprocessor` it calls (`src/theory/theory_preprocessor.cpp`),
with term formula removal (`RemoveTermFormulas::runCurrent`,
`src/smt/term_formula_removal.cpp`).

Each assertion is rewritten, then traversed (`theoryPreprocess`). Before its
children, a node may be replaced by its purification skolem (term formula
removal), with a lemma the first time: a non-Boolean `ite` (lemma
`(ite c (= k t₁) (= k t₂))`), and a Boolean term below a non-Boolean operator
(lemma `(= k t)`). Otherwise its children are traversed, and the result is
rewritten, or if rewriting does not change it, rewritten by its theory's
`ppRewrite` (not for equalities) and then rewritten; a changed result is
traversed again. The lemmas are preprocessed in turn, and their own lemmas too.
The assertion is replaced by the result, and the lemmas are added after the last
assertion, split into conjuncts.

As in cvc5, whose traversal uses a stack, the children of a node are visited
from the last to the first, which fixes the order of the lemmas.

The traversal's cache, keyed by the node and its context (inside a term or
not), and the set of terms that have skolems, last for the whole pass, as
cvc5's last for the whole run, so a term already purified in an earlier
assertion gets no second lemma. Quantifier bodies are not traversed.

Ported theory hooks: arithmetic (`TheoryArith::ppRewrite`), bit-vectors
(`TheoryBV::ppRewrite`), datatypes (`TheoryDatatypes::ppRewrite`, but for
tuple updaters) and strings (`TheoryStrings::ppRewrite`). Sets and UF have
nothing to do on the input telos supports. Not ported: arrays (`select` over
`store` and store reordering at indices known disequal), which the rewriter
already does in the cases that arise without non-clausal simplification.

Every step is certified (`Telos/Preprocess/SkolemSteps.lean`): the pass is a
rewrite of the conjunction of the assertions.
-/

namespace Telos.Preprocess

open Node

/-- The state of cvc5's `TheoryPreprocessor`. -/
structure TppState where
  /-- `d_cache`: the result for each node in each context. -/
  cache : Std.HashMap (Key × Nat) ((n : Node) × Rw n) := {}
  /-- `RemoveTermFormulas`'s skolem cache: the terms that have a skolem. -/
  purified : Std.HashSet Key := {}
  /-- The lemmas of the current assertion (`newLemmas`). -/
  lemmas : Array (Rw mkTrue) := #[]
  /-- The lemmas of the assertions processed so far, in order. -/
  allLemmas : Array (Rw mkTrue) := #[]

abbrev TppM := StateM TppState

/-! Updates of the state's fields take the field out before changing it, so
that it is not shared and is updated in place (`{ s with f := s.f.insert … }`
copies `s.f` on every update, which is quadratic). -/

def updCache (f : Std.HashMap (Key × Nat) ((n : Node) × Rw n) →
    Std.HashMap (Key × Nat) ((n : Node) × Rw n)) : TppM Unit :=
  modify fun s =>
    let c := s.cache
    let s := { s with cache := {} }
    { s with cache := f c }

def updPurified (f : Std.HashSet Key → Std.HashSet Key) : TppM Unit :=
  modify fun s =>
    let c := s.purified
    let s := { s with purified := {} }
    { s with purified := f c }

def updLemmas (f : Array (Rw mkTrue) → Array (Rw mkTrue)) : TppM Unit :=
  modify fun s =>
    let c := s.lemmas
    let s := { s with lemmas := #[] }
    { s with lemmas := f c }

/-- cvc5's `RtfTermContext::hasNestedTermChildren`: the children of `n` are
inside a term. -/
def hasNestedTermChildren (n : Node) : Bool :=
  n.getKind.theoryId != .THEORY_BOOL && n.getKind != .EQUAL

/-- cvc5's `RtfTermContext::computeValue`: `1` for inside a quantifier, plus
`2` for inside a term. -/
def childContext (n : Node) (val : Nat) : Nat :=
  if n.getKind.isQuantifier then (if val % 2 == 0 then val + 1 else val)
  else if hasNestedTermChildren n then (if val < 2 then val + 2 else val)
  else val

def addLemma (l : Option (Rw mkTrue)) : TppM Unit :=
  if let some l := l then updLemmas (·.push l) else pure ()

/-- `RemoveTermFormulas::runCurrent`: `n` replaced by its purification skolem,
if it is a non-Boolean `ite`, or a Boolean term inside a term (`inTerm`) that is
not itself a purification skolem; with a lemma, the first time. -/
def removeTermFormulas (n : Node) (inTerm : Bool) : TppM (Option (Rw n)) := do
  let isBool := n.typeHint == some .boolean
  let isIte := n.getKind == .ITE && !isBool
  let isPurify := match n with | .skolem .PURIFY _ => true | _ => false
  if !isIte && !(isBool && inTerm && !isPurify) then return none
  let some step := Profile.time "tpp" (fun _ => "purifyStep") fun _ => purifyStep n | return none
  if !(← get).purified.contains ⟨n⟩ then
    updPurified (·.insert ⟨n⟩)
    addLemma <| Profile.time "tpp" (fun _ => "lemma") fun _ => if isIte then
        -- `ite_eq` proves `(ite c (= n t₁) (= n t₂))`; then `n` is purified
        (lemmaBy [stepWith .ite_eq [n.toEo]]).map fun l => l.trans (replaceRw n step l.1)
      else lemmaBy [stepWith .skolem_intro [(mkPurifySkolem n).toEo]]
  return some step

/-- `TheoryEngine::ppRewrite`, for the ported theories: the theory of `n`
eliminates it, with a lemma. -/
def ppRewrite (n : Node) : Option (Rw n × Option (Rw mkTrue)) :=
  match theoryOf n with
  | .THEORY_ARITH => arithPpRewrite n
  | .THEORY_BV => (bvPpRewrite n).map (·, none)
  | .THEORY_DATATYPES => (dtPpRewrite n).map (·, none)
  | .THEORY_STRINGS => stringsPpRewrite n
  | _ => none

/-- `preprocessWithProof`: `ppRewrite`, except for equalities, then rewriting. -/
def preprocessWithProof (n : Node) : TppM (Rw n) := do
  if n.getKind == .EQUAL then return Rw.id n
  match ppRewrite n with
  | some (r, lem) =>
    addLemma lem
    return r.trans (rewriteCert r.1)
  | none => return Rw.id n

/-- The cached result for `n` in context `val`. -/
def findCache (n : Node) (val : Nat) : TppM (Option (Rw n)) := do
  match (← get).cache.get? (⟨n⟩, val) with
  | some ⟨n', r⟩ => return if h : n' = n then some (h ▸ r) else none
  | none => return none

/-- `TheoryPreprocessor::theoryPreprocess`, for `n` in context `val`. -/
partial def theoryPreprocess (n : Node) (val : Nat) : TppM (Rw n) := do
  if let some r ← findCache n val then return r
  let res ← do
    if let some r ← removeTermFormulas n (2 ≤ val) then pure r
    else
      let traverse := !n.getKind.isQuantifier && n.getNumChildren > 0
      let r₁ ← if traverse then
          -- cvc5 pushes the children on a stack: the last is visited first
          rewriteChildren (fun c => theoryPreprocess c (childContext n val)) n (reverse := true)
        else pure (Rw.id n)
      let ret := r₁.1
      -- cvc5 rewrites `ret` here, a cache hit when the children did not change
      -- (`n` is then a subterm of a rewritten term); telos's rewriter has no
      -- cache across calls, so it rewrites only a changed node.
      let r₂ : Rw ret := if traverse && ret != n then Profile.time "tpp" (fun _ => "rewrite") fun _ => rewriteCert ret else Rw.id ret
      let r₂ ← if r₂.1 == ret then preprocessWithProof ret else pure r₂
      if r₂.1 == ret then pure r₁
      else
        -- changed: traverse the result again
        let r₃ ← theoryPreprocess r₂.1 val
        pure (r₁.trans (r₂.trans r₃))
  updCache (·.insert (⟨n⟩, val) ⟨n, res⟩)
  return res

/-- `TheoryPreprocessor::preprocessInternal`: rewrite, then traverse. -/
def preprocessInternal (n : Node) : TppM (Rw n) := do
  let ir := rewriteCert n
  return ir.trans (← theoryPreprocess ir.1 0)

/-- `TheoryPreprocessor::preprocess`: the assertion `a` preprocessed; its
lemmas, preprocessed too (with theirs), are added to `allLemmas`. -/
def preprocessAssertion (a : Node) : TppM (Rw a) := do
  modify fun s => { s with lemmas := #[] }
  let r ← preprocessInternal a
  let mut i := 0
  while i < (← get).lemmas.size do
    let l := (← get).lemmas[i]!
    let l' := l.trans (← preprocessInternal l.1)
    updLemmas (·.set! i l')
    i := i + 1
  modify fun s =>
    let all := s.allLemmas
    let lems := s.lemmas
    let s := { s with allLemmas := #[], lemmas := #[] }
    { s with allLemmas := all ++ lems }
  return r

/-- The `theory-preprocess` pass: each assertion replaced by its preprocessed
form, then the lemmas added. -/
def Pipeline.theoryPreprocess {input : Node} (p : Pipeline input) : Pipeline input :=
  if Pipeline.inConflict p then p
  else
    -- the assertions in order (not the definitions slot), with the state threaded
    let as := (Pipeline.assertions p).toList
    let (rs, st) := (as.mapM fun a => do
      let r ← preprocessAssertion a
      pure (⟨a, r⟩ : (c : Node) × Rw c)).run {}
    let rs := rs.toArray
    let q := Pipeline.mapConjuncts p fun i c =>
      match rs[i]? with
      | some ⟨a, r⟩ => if h : a = c then h ▸ r else Rw.id c
      | none => Rw.id c
    let lems := Profile.time "tpp" (fun _ => "splitLemma") fun _ => st.allLemmas.toList.flatMap splitLemma
    Pipeline.conflict? (Pipeline.pushLemmas q lems)

end Telos.Preprocess
