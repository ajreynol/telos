import TelosProofs.Congruence
import Cpc.Proofs.ProvenFromEmpty

/-!
# Certified steps are equivalences

`Certified n m` (`Telos/Rewriter/Certified.lean`) chains CPC command lists, each
accepted by Logos's checker from the empty state with last proven fact `(= n m)`.
Logos proves that such a fact is well typed and true in every well-formed model
(`proven_from_empty_valid`, from its checker soundness proof for every CPC rule).
Hence `Certified n m` implies `n.Equiv m` (`Certified.equiv`), with no proof per
rule.
-/

open Eo

namespace Telos

theorem ProvesEq.equiv {cs : CCmdList} {n m : Node} (h : ProvesEq cs n m) : n.Equiv m := by
  rw [Node.equiv_iff_termEquiv]
  exact proven_from_empty_valid cs _ h.1 h.2.1 h.2.2

theorem forall₂_set {α : Type} {R : α → α → Prop} :
    ∀ (l : List α) (i : Nat) (x : α) (hi : i < l.length),
      (∀ y ∈ l, R y y) → R l[i] x → List.Forall₂ R l (l.set i x)
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | y :: l, 0, x, _, hrefl, hx => by
    simpa using List.Forall₂.cons hx (List.forall₂_same.2 fun z hz => hrefl z (by simp [hz]))
  | y :: l, i + 1, x, hi, hrefl, hx => by
    simp only [List.set_cons_succ]
    exact List.Forall₂.cons (hrefl y (by simp))
      (forall₂_set l i x (by simpa using hi) (fun z hz => hrefl z (by simp [hz])) (by simpa using hx))

theorem forall₂_of_getElem {R : Node → Node → Prop} {cs ds : Array Node}
    (hsize : cs.size = ds.size) (h : ∀ i (hi : i < cs.size), R cs[i] (ds[i]'(hsize ▸ hi))) :
    List.Forall₂ R cs.toList ds.toList := by
  rw [List.forall₂_iff_get]
  exact ⟨by simpa using hsize, fun i h₁ h₂ => by simpa using h i (by simpa using h₁)⟩

/-- **Certified rewrites are equivalences.** -/
theorem Certified.equiv {n m : Node} (h : Certified n m) (hn : n.WellTyped) : n.Equiv m := by
  induction h with
  | refl n => exact Node.Equiv.refl n hn
  | step cs hs _ ih =>
    have h₁ := ProvesEq.equiv hs
    exact h₁.trans (ih h₁.wellTyped_right)
  | @congrArg op cs m i c' hi hop hwt _ _ ihc ih =>
    have hci : cs[i].Equiv c' := ihc (hwt _ (Array.getElem_mem_toList hi))
    have hch : List.Forall₂ Node.Equiv cs.toList (cs.set i c').toList := by
      rw [Array.toList_set]
      exact forall₂_set _ i c' (by simpa using hi)
        (fun y hy => Node.Equiv.refl y (hwt y hy)) (by simpa using hci)
    have h₁ := Node.Equiv.congr hop hn hch
    exact h₁.trans (ih h₁.wellTyped_right)
  | @congr op cs ds m hsize hop hwt _ _ ihc ih =>
    have hch : List.Forall₂ Node.Equiv cs.toList ds.toList :=
      forall₂_of_getElem hsize fun i hi => ihc i hi (hwt _ (Array.getElem_mem_toList hi))
    have h₁ := Node.Equiv.congr hop hn hch
    exact h₁.trans (ih h₁.wellTyped_right)
  | @congrBody k vs body body' m pats hk hb _ _ ihb ih =>
    have hk' : k = .FORALL ∨ k = .EXISTS := by cases k <;> simp_all [Kind.isQuantifier]
    have h₁ := Node.Equiv.congr_binder hk' rfl hn (ihb hb)
    exact h₁.trans (ih h₁.wellTyped_right)

end Telos
