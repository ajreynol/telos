import Telos.Rewriter.Theory.Common
import Telos.Core.Node.Order

/-!
# The assertion pipeline

A port of cvc5's `AssertionPipeline` (`src/preprocessing/assertion_pipeline.cpp`),
the list of assertions that preprocessing passes transform.

The pipeline is one node: the conjunction of its assertions, `(and a₁ … aₙ)`, as
a certified rewrite (`Rw`) of the conjunction of the input assertions. A pass is
then a rewrite of the conjunction, made of CPC-checked steps (rewriting an
assertion is congruence below `and`; splitting a conjunction is `aci_norm`), and
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

namespace Pipeline

/-- The assertions, in order. -/
def assertions {input : Node} (p : Pipeline input) : Array Node :=
  match p.1 with
  | .app (.kind .AND) cs => cs
  | n => #[n]

/-- Whether the pipeline is in conflict (`isInConflict`). -/
def inConflict {input : Node} (p : Pipeline input) : Bool := p.1 == mkFalse

/-- The pipeline with the assertions `as` in place of the current ones, if
`aci_norm` proves the two conjunctions equal: they have the same conjuncts, up
to nested conjunctions, `true` and duplicates. -/
def rearrange {input : Node} (p : Pipeline input) (as : List Node) : Option (Pipeline input) :=
  let target := mkNode .AND as.toArray
  if target == p.1 then some p
  else p.next? fun m => checkBy .aci_norm m target

/-- `markConflict`: if an assertion is `false`, the pipeline is `false`
(`absorb`). -/
def conflict? {input : Node} (p : Pipeline input) : Pipeline input :=
  if !inConflict p && (assertions p).contains mkFalse then
    (p.next? fun m => checkBy .absorb m mkFalse).getD p
  else p

end Pipeline

/-- The assertions that `AssertionPipeline::push_back` adds for `n`: its
conjuncts, flattened, in order. -/
partial def flattenAnd : Node → List Node
  | .app (.kind .AND) cs => cs.toList.flatMap flattenAnd
  | n => [n]

/-- The pipeline of cvc5's `ProcessAssertions`, before the passes: the input
assertions pushed one by one (`push_back`, which splits conjunctions), then
`true`. -/
def Pipeline.init (as : List Node) : Pipeline (inputNode as) :=
  let p : Pipeline (inputNode as) := Rw.id _
  let pushed := as.flatMap flattenAnd ++ [mkTrue]
  Pipeline.conflict? ((Pipeline.rearrange p pushed).getD p)

end Telos.Preprocess
