import Telos.Core.Node.Node

/-!
# Semantically justified steps

A `Certified.semantic p` step rewrites `n` to `m` without CPC and without
Logos's checker. `p : SemProc` names the procedure, and:

* `p.Ok n m` is its side condition, which telos decides on its own nodes (with
  `Node.decEq`, constant time on shared subterms, so nothing is traversed as a
  tree);
* `verification/TelosProofs/Core/Semantic.lean` proves
  `p.Ok n m → n.WellTyped → n.Equiv m` (`SemProc.equiv`) once, from Logos's
  semantics, so `Certified.equiv` covers the step.

Unlike CPC steps, these steps have no CPC proof to print.

Procedures:

* `reorg`: two conjunctions with the same conjuncts, up to nesting, `true` and
  repetition (splitting the pipeline's conjuncts, adding `true` for lemmas).
-/

namespace Telos

namespace Node

/-- The conjuncts of `n`: the conjuncts of a conjunction, flattened, without
`true`; any other node is its own conjunct. -/
def conjuncts : Node → List Node
  | .app (.kind .AND) cs => cs.attach.toList.flatMap fun ⟨c, _⟩ => conjuncts c
  | .const (.boolean true) => []
  | n => [n]
termination_by n => sizeOf n
decreasing_by have := Array.sizeOf_lt_of_mem ‹_›; simp_all; omega

/-- Every conjunction of `n`, at the conjunction levels, has at least two
conjuncts (as a conjunction must, to translate). -/
def andShapeOk : Node → Bool
  | .app (.kind .AND) cs => 2 ≤ cs.size && cs.attach.all fun ⟨c, _⟩ => andShapeOk c
  | _ => true
termination_by n => sizeOf n
decreasing_by have := Array.sizeOf_lt_of_mem ‹_›; simp_all; omega

/-- Whether `n` is a conjunction `(and …)`. -/
def isAndApp : Node → Bool
  | .app (.kind .AND) _ => true
  | _ => false

end Node

/-- The semantically justified procedures. -/
inductive SemProc where
  /-- Same conjuncts, up to nesting, `true` and repetition. -/
  | reorg

/-- The side condition of a step from `n` to `m`. -/
def SemProc.Ok : SemProc → Node → Node → Prop
  | .reorg, n, m =>
    n.isAndApp = true ∧ m.isAndApp = true ∧ n.andShapeOk = true ∧ m.andShapeOk = true ∧
      (∀ c ∈ m.conjuncts, c ∈ n.conjuncts) ∧ (∀ c ∈ n.conjuncts, c ∈ m.conjuncts)

instance (p : SemProc) (n m : Node) : Decidable (p.Ok n m) := by
  cases p <;> unfold SemProc.Ok <;> infer_instance

end Telos
