import Std.Data.HashSet
import Cpc.Logos
import Telos.Core.Node.Key
import Telos.Core.Node.SmtTypeFast

/-!
# `aci_norm` for conjunctions and disjunctions

CPC's `aci_norm` accepts `(= n m)` when `n` and `m` have the same normal form up
to associativity, commutativity, idempotence and the unit. For `and` and `or`,
telos decides a condition that implies it on its own nodes, without
translating them: the two have the same leaves (`Aci.leaves`: the operands,
flattened, without the unit), as sets. The step is then `StaticProc.aci`
(`Telos/Core/Static.lean`), and `verification/TelosProofs/Core/AciNorm.lean`
proves that Logos accepts the command.
-/

open Eo
open Smtm

namespace Telos.Aci

/-- The operands of `n` for the operator `k` with unit `u`: those of an
application of `k`, flattened, without `u`; any other node is its own operand. -/
def leaves (k : Kind) (u : Bool) : Node → List Node
  | .const (.boolean b) => if b = u then [] else [.const (.boolean b)]
  | .app (.kind k') cs =>
    if k' = k ∧ 2 ≤ cs.size then cs.attach.toList.flatMap fun ⟨c, _⟩ => leaves k u c
    else [.app (.kind k') cs]
  | n => [n]
termination_by n => sizeOf n
decreasing_by have := Array.sizeOf_lt_of_mem ‹_›; simp_all; omega

/-- The unit of `and` or `or`. -/
def unit? : Kind → Option Bool
  | .AND => some true
  | .OR => some false
  | _ => none

/-- `n` is an application of `and` or `or`, with the leaves of `m`. -/
def LeavesOk (n m : Node) : Prop :=
  match n with
  | .app (.kind k) cs => match unit? k with
    | some u => 2 ≤ cs.size ∧ (∀ x ∈ leaves k u m, x ∈ leaves k u (.app (.kind k) cs)) ∧
        (∀ x ∈ leaves k u (.app (.kind k) cs), x ∈ leaves k u m)
    | none => False
  | _ => False

/-- The side condition of a step from `n` to `m`. -/
def Ok (n m : Node) : Prop :=
  LeavesOk n m ∧ (Node.eqNode n m).smtTypeF = .Bool

/-- Whether every node of `as` is one of `bs`, by a hash set of `bs`. -/
def subset (as bs : List Node) : Bool :=
  let s : Std.HashSet Key := Std.HashSet.ofList (bs.map Key.mk)
  as.all fun c => s.contains ⟨c⟩

theorem subset_mem {as bs : List Node} (h : subset as bs = true) : ∀ c ∈ as, c ∈ bs := by
  intro c hc
  simp only [subset, List.all_eq_true, Std.HashSet.contains_ofList] at h
  have := h c hc
  simp only [List.contains_iff_mem, List.mem_map] at this
  obtain ⟨d, hd, e⟩ := this
  cases e
  exact hd

/-- The side condition, decided in time linear in the operands. -/
def check (n m : Node) : Bool :=
  (match n with
   | .app (.kind k) cs => match unit? k with
     | some u =>
       let ln := leaves k u (.app (.kind k) cs)
       let lm := leaves k u m
       2 ≤ cs.size && subset lm ln && subset ln lm
     | none => false
   | _ => false) && (Node.eqNode n m).smtTypeF = .Bool

theorem check_ok {n m : Node} (h : check n m = true) : Ok n m := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  have h := h.1
  unfold LeavesOk
  split at h
  · split at h
    · rename_i u hu
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1, subset_mem h.1.2, subset_mem h.2⟩
    · cases h
  · cases h

end Telos.Aci

namespace Telos.AciConcat

/-- `(str.++ cs…)` is a concatenation of strings, whose nil is `""`. -/
def isConcat (cs : Array Node) : Bool :=
  2 ≤ cs.size && cs[0]?.any fun c => c.smtTypeF = .Seq .Char

/-- The components of `n`: those of a concatenation, flattened, without `""`;
any other node is its own component. -/
def leaves : Node → List Node
  | .const (.string w) => if w = [] then [] else [.const (.string w)]
  | .app (.kind k) cs =>
    if k = .STRING_CONCAT ∧ isConcat cs = true then cs.attach.toList.flatMap fun ⟨c, _⟩ => leaves c
    else [.app (.kind k) cs]
  | n => [n]
termination_by n => sizeOf n
decreasing_by have := Array.sizeOf_lt_of_mem ‹_›; simp_all; omega

/-- The side condition of a step from `n`, a concatenation of strings, to `m`:
the same components in the same order. -/
def Ok (n m : Node) : Prop :=
  (match n with
   | .app (.kind .STRING_CONCAT) cs => isConcat cs = true
   | _ => False) ∧ leaves n = leaves m ∧ n.smtTypeF = .Seq .Char ∧ m.smtTypeF = .Seq .Char

instance (n m : Node) : Decidable (Ok n m) := by
  unfold Ok
  have : Decidable (match n with
   | .app (.kind .STRING_CONCAT) cs => isConcat cs = true
   | _ => False) := by split <;> infer_instance
  infer_instance

end Telos.AciConcat
