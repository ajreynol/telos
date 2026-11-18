import Telos.Rewriter.Theory.Common
import Telos.Preprocess.Conjunctions
import Telos.Core.Node.Order

/-!
# The assertion pipeline

A port of cvc5's `AssertionPipeline` (`src/preprocessing/assertion_pipeline.cpp`),
the list of assertions that preprocessing passes transform.

The pipeline is one node: the conjunction of its assertions, `(and a₁ … aₙ)`, as
a certified rewrite (`Rw`) of the conjunction of the input assertions. A pass is
then a rewrite of the conjunction, made of CPC-checked steps (rewriting an
assertion is congruence below `and`; splitting a conjunction is `aci_norm`;
adding a lemma `L` is `aci_norm` to add a conjunct `true`, then a rewrite
`true → L`, `pushLemmas`), and
the preprocessed assertions are equivalent to the input ones by the theorem that
covers every certified rewrite (`Certified.equiv`). No pass needs a proof of its
own.

As in cvc5, the input is followed by the assertion `true` (`ProcessAssertions`
pushes it as a placeholder for new assertions), so the conjunction has at least
two children. A conflict, an assertion that is `false`, makes the pipeline the
single assertion `false` (`markConflict`); the conjunction is then the node
`false`.
-/

namespace Telos.Preprocess

open Node

/-- The conjunction of the input assertions and `true`, the node that
preprocessing rewrites. -/
def inputNode (as : List Node) : Node := mkNode .AND (as ++ [mkTrue]).toArray

/-- cvc5's `AssertionPipeline`: the conjunction of the assertions, certified
equivalent to the input `input`. -/
abbrev Pipeline (input : Node) := Rw input

/-- The assertions that `AssertionPipeline::push_back` adds for `n`: its
conjuncts, flattened, in order. -/
partial def flattenAnd : Node → List Node
  | .app (.kind .AND) cs => cs.toList.flatMap flattenAnd
  | n => [n]

namespace Pipeline

/-- The assertions, in order. -/
def assertions {input : Node} (p : Pipeline input) : Array Node :=
  match p.1 with
  | .app (.kind .AND) cs => cs
  | n => #[n]

/-- Whether the pipeline is in conflict (`isInConflict`). -/
def inConflict {input : Node} (p : Pipeline input) : Bool := p.1 == mkFalse

/-- The pipeline with the assertions `as` in place of the current ones, if the
two conjunctions have the same conjuncts, up to nested conjunctions, `true` and
duplicates: by `andReorg`, linear, or else `aci_norm`. -/
def rearrange {input : Node} (p : Pipeline input) (as : List Node) : Option (Pipeline input) :=
  let target := mkNode .AND as.toArray
  if target == p.1 then some p
  else p.next? fun m => (andReorg m target).orElse fun _ => checkBy .aci_norm m target

/-- `markConflict`: if an assertion is `false`, the pipeline is `false`
(`absorb`). -/
def conflict? {input : Node} (p : Pipeline input) : Pipeline input :=
  if !inConflict p && (assertions p).contains mkFalse then
    (p.next? fun m => checkBy .absorb m mkFalse).getD p
  else p

/-- Replace each assertion `a` by its rewrite `f a` (`AssertionPipeline::replace`,
for every assertion), by congruence below the conjunction; an assertion that
becomes `false` is a conflict. -/
def mapAssertions {input : Node} (p : Pipeline input) (f : (c : Node) → Rw c) : Pipeline input :=
  if inConflict p then p
  else
    match h : p.1 with
    | .app (.kind .AND) cs =>
      let r : Rw (.app (.kind .AND) cs) := Rw.congr (.kind .AND) cs f rfl (.inl rfl)
      conflict? (p.trans (h ▸ r))
    | _ => p

/-- The `true` assertions from position `k` on replaced by the lemmas `lems`,
certified rewrites of `true`, in one congruence step below the conjunction. -/
def setLemmas {input : Node} (p : Pipeline input) (k : Nat) (lems : Array (Rw mkTrue)) :
    Pipeline input :=
  match h : p.1 with
  | .app (.kind .AND) cs =>
    let f : Node × Nat → (c : Node) × Rw c := fun (c, i) =>
      ⟨c, if hi : k ≤ i ∧ i - k < lems.size then
            if hc : c = mkTrue then hc ▸ lems[i - k] else Rw.id c
          else Rw.id c⟩
    let rs := cs.toList.zipIdx.map f
    have hrs : rs.map (·.1) = cs.toList := by
      simp only [rs, List.map_map]
      exact List.zipIdx_map_fst 0 _
    p.trans (h ▸ Rw.congrList (.kind .AND) cs rs hrs rfl (.inl rfl))
  | _ => p

/-- `pushBackTrusted` for each lemma, in order: a lemma, a certified rewrite of
`true`, is added after the last assertion. The lemmas are given split into
their conjuncts, as `push_back` splits them (`splitLemma`). The conjunction gets
a `true` per lemma (`andReorg`), and they are rewritten to the lemmas (one
congruence step). A lemma that is still a conjunction is split by a second
`andReorg` step. -/
def pushLemmas {input : Node} (p : Pipeline input) (lems : List (Rw mkTrue)) : Pipeline input :=
  if lems.isEmpty || inConflict p then p
  else
    let as := (assertions p).toList
    match rearrange p (as ++ lems.map fun _ => mkTrue) with
    | none => p
    | some q =>
      let q := setLemmas q as.length lems.toArray
      let bs := (assertions q).toList
      let q := if (bs.drop as.length).any (·.getKind == .AND) then
          let flat := bs.take as.length ++ (bs.drop as.length).flatMap flattenAnd
          (rearrange q flat).getD q
        else q
      conflict? q

end Pipeline

/-- The pipeline of cvc5's `ProcessAssertions`, before the passes: the input
assertions pushed one by one (`push_back`, which splits conjunctions), then
`true`. -/
def Pipeline.init (as : List Node) : Pipeline (inputNode as) :=
  let p : Pipeline (inputNode as) := Rw.id _
  let pushed := as.flatMap flattenAnd ++ [mkTrue]
  Pipeline.conflict? ((Pipeline.rearrange p pushed).getD p)

end Telos.Preprocess
