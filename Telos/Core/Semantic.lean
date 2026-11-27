import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Learn
import Telos.Core.StrSplit

/-!
# Semantically justified steps

A `Certified.semantic p` step rewrites `n` to `m` without CPC and without
Logos's checker. `p : SemProc` names the procedure, and:

* `p.Ok n m` is its side condition, which telos decides on its own nodes by
  `p.check n m`, in linear time (`SemProc.check_ok`): hash sets of nodes, which
  hash and compare in constant time on shared subterms, so nothing is traversed
  as a tree;
* `verification/TelosProofs/Core/Semantic.lean` proves
  `p.Ok n m → n.WellTyped → n.Equiv m` (`SemProc.equiv`) once, from Logos's
  semantics, so `Certified.equiv` covers the step.

Unlike CPC steps, these steps have no CPC proof to print.

Procedures:

* `reorg`: two conjunctions with the same conjuncts, up to nesting, `true` and
  repetition (splitting the pipeline's conjuncts, adding `true` for lemmas);
* `learn`: a conjunction with literals added, learned by Boolean propagation
  (`Telos/Core/Learn.lean`), or `false` if propagation finds a conflict;
* `strSplit`: an equality of concatenations of strings split into those of
  prefixes of equal lengths and of the suffixes (`Telos/Core/StrSplit.lean`).
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
  /-- Literals learned by Boolean propagation, added (`Telos/Core/Learn.lean`). -/
  | learn (L : LearnPlan)
  /-- An equality of concatenations split after `i` and `j` components
  (`Telos/Core/StrSplit.lean`). -/
  | strSplit (i j : Nat)

/-- The side condition of a step from `n` to `m`. -/
def SemProc.Ok : SemProc → Node → Node → Prop
  | .reorg, n, m =>
    n.isAndApp = true ∧ m.isAndApp = true ∧ n.andShapeOk = true ∧ m.andShapeOk = true ∧
      (∀ c ∈ m.conjuncts, c ∈ n.conjuncts) ∧ (∀ c ∈ n.conjuncts, c ∈ m.conjuncts)
  | .learn L, n, m => L.Ok n m = true
  | .strSplit i j, n, m => StrSplit.ok i j n m = true

instance (p : SemProc) (n m : Node) : Decidable (p.Ok n m) := by
  cases p <;> unfold SemProc.Ok <;> infer_instance

/-- Whether every node of `as` is one of `bs`, by a hash set of `bs`. -/
def subsetBy (as bs : List Node) : Bool :=
  let s : Std.HashSet Key := Std.HashSet.ofList (bs.map Key.mk)
  as.all fun c => s.contains ⟨c⟩

theorem subsetBy_mem {as bs : List Node} (h : subsetBy as bs = true) : ∀ c ∈ as, c ∈ bs := by
  intro c hc
  simp only [subsetBy, List.all_eq_true, Std.HashSet.contains_ofList] at h
  have := h c hc
  simp only [List.contains_iff_mem, List.mem_map] at this
  obtain ⟨d, hd, e⟩ := this
  cases e
  exact hd

/-- The side condition of `p`, decided in linear time. -/
def SemProc.check : SemProc → Node → Node → Bool
  | .reorg, n, m =>
    n.isAndApp && m.isAndApp && n.andShapeOk && m.andShapeOk &&
      (let cn := n.conjuncts; let cm := m.conjuncts; subsetBy cm cn && subsetBy cn cm)
  | .learn L, n, m => L.Ok n m
  | .strSplit i j, n, m => StrSplit.ok i j n m

theorem SemProc.check_ok {p : SemProc} {n m : Node} (h : p.check n m = true) : p.Ok n m := by
  cases p
  case learn L => exact h
  case strSplit i j => exact h
  simp only [SemProc.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅, h₆⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, subsetBy_mem h₅, subsetBy_mem h₆⟩

end Telos
