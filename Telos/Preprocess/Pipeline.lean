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
`true → L`, `pushLemmas`; the reorganizations are semantic steps,
`SemProc.reorg`), and
the preprocessed assertions are equivalent to the input ones by the theorem that
covers every certified rewrite (`Certified.equiv`). No pass needs a proof of its
own.

As in cvc5, the input is followed by the assertion `true` (`ProcessAssertions`
pushes it as a placeholder for new assertions). The last conjunct is not an
assertion but the **definitions** slot: cvc5's top-level substitutions
(`TopLevelSubstitutions`), the equations `(= x t)` of the variables solved by
non-clausal simplification, as `true` (none), the equation, or their
conjunction. They are part of the conjunction, so that the preprocessed
assertions and the definitions together are equivalent to the input
(`Telos.preprocess_correct`), and they are printed as `define-fun`s. A
conflict, an assertion that is `false`, makes the pipeline the single assertion
`false` (`markConflict`); the conjunction is then the node `false`.
-/

namespace Telos.Preprocess

open Node

/-- The conjunction of the input assertions, `true` (the placeholder) and `true`
(the empty definitions slot): the node that preprocessing rewrites. -/
def inputNode (as : List Node) : Node := mkNode .AND (as ++ [mkTrue, mkTrue]).toArray

/-- cvc5's `AssertionPipeline`: the conjunction of the assertions, certified
equivalent to the input `input`. -/
abbrev Pipeline (input : Node) := Rw input

/-- The assertions that `AssertionPipeline::push_back` adds for `n`: its
conjuncts, flattened, in order. -/
partial def flattenAnd : Node → List Node
  | .app (.kind .AND) cs => cs.toList.flatMap flattenAnd
  | n => [n]

namespace Pipeline

/-- The assertions, in order: the conjuncts but the definitions slot. -/
def assertions {input : Node} (p : Pipeline input) : Array Node :=
  match p.1 with
  | .app (.kind .AND) cs => cs.pop
  | n => #[n]

/-- The definitions slot: the last conjunct (`true` in conflict). -/
def slot {input : Node} (p : Pipeline input) : Node :=
  match p.1 with
  | .app (.kind .AND) cs => cs.back?.getD mkTrue
  | _ => mkTrue

/-- The definitions, the equations `(= x t)` of the solved variables. -/
def defs {input : Node} (p : Pipeline input) : List Node :=
  (flattenAnd (slot p)).filter (· != mkTrue)

/-- Whether the pipeline is in conflict (`isInConflict`). -/
def inConflict {input : Node} (p : Pipeline input) : Bool := p.1 == mkFalse

/-- The pipeline with the assertions `as` in place of the current ones, if the
two conjunctions have the same conjuncts, up to nested conjunctions, `true` and
duplicates: by a semantic step (`SemProc.reorg`, decided in linear time with
hash sets), or else by a CPC proof, `andReorg` or `aci_norm`. -/
def rearrange {input : Node} (p : Pipeline input) (as : List Node) : Option (Pipeline input) :=
  let target := mkNode .AND (as ++ [slot p]).toArray
  if target == p.1 then some p
  else Profile.time "pipeline" (fun _ => "rearrange") fun _ =>
    if h : SemProc.reorg.check p.1 target = true then
      some (p.trans ⟨target, .semantic .reorg (SemProc.check_ok h) (.refl target)⟩)
    else p.next? fun m => (andReorg m target).orElse fun _ => checkBy .aci_norm m target

/-- `markConflict`: if an assertion is `false`, the pipeline is `false`
(`absorb`). -/
def conflict? {input : Node} (p : Pipeline input) : Pipeline input :=
  if !inConflict p && (assertions p).contains mkFalse then
    Profile.time "pipeline" (fun _ => "conflict") fun _ => (p.next? fun m => checkBy .absorb m mkFalse).getD p
  else p

/-- The conjunct at each position `i` rewritten by `g i`, in one congruence
step below the conjunction. -/
def mapConjuncts {input : Node} (p : Pipeline input) (g : Nat → (c : Node) → Rw c) :
    Pipeline input :=
  match h : p.1 with
  | .app (.kind .AND) cs =>
    let f : Node × Nat → (c : Node) × Rw c := fun (c, i) => ⟨c, g i c⟩
    let rs := cs.toList.zipIdx.map f
    have hrs : rs.map (·.1) = cs.toList := by
      simp only [rs, List.map_map]
      exact List.zipIdx_map_fst 0 _
    Profile.time "pipeline" (fun _ => "mapConjuncts") fun _ =>
      p.trans (h ▸ Rw.congrList (.kind .AND) cs rs hrs rfl (.inl rfl))
  | _ => p

/-- The number of conjuncts, with the definitions slot. -/
def numConjuncts {input : Node} (p : Pipeline input) : Nat := p.1.getNumChildren

/-- Replace each assertion `a` by its rewrite `f a` (`AssertionPipeline::replace`,
for every assertion), by congruence below the conjunction; an assertion that
becomes `false` is a conflict. The definitions are not rewritten. -/
def mapAssertions {input : Node} (p : Pipeline input) (f : (c : Node) → Rw c) : Pipeline input :=
  if inConflict p then p
  else
    let last := numConjuncts p - 1
    conflict? (mapConjuncts p fun i c => if i < last then f c else Rw.id c)

/-- The `true` assertions from position `k` on replaced by the lemmas `lems`,
certified rewrites of `true`, in one congruence step below the conjunction. -/
def setLemmas {input : Node} (p : Pipeline input) (k : Nat) (lems : Array (Rw mkTrue)) :
    Pipeline input :=
  mapConjuncts p fun i c =>
    if hi : k ≤ i ∧ i - k < lems.size then
      if hc : c = mkTrue then hc ▸ lems[i - k] else Rw.id c
    else Rw.id c

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
