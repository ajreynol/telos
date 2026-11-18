import Telos.Core.Node.Node

/-!
# Decidable equality of nodes

Lean cannot derive `DecidableEq` for `Node` and `Op`, which are mutual and nested
through `Array`, so it is written out here. This is structural equality, the
equality the specification uses. (cvc5 compares node ids; with hash-consing the
two coincide.)
-/

namespace Telos

mutual

def Node.decEq : (a b : Node) → Decidable (a = b)
  | .const c, .const d =>
      if h : c = d then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .var n T, .var m U =>
      if h : n = m ∧ T = U then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
      else isFalse fun e => by cases e; exact h ⟨rfl, rfl⟩
  | .boundVar n T, .boundVar m U =>
      if h : n = m ∧ T = U then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
      else isFalse fun e => by cases e; exact h ⟨rfl, rfl⟩
  | .app o cs, .app p ds =>
      match Op.decEq o p, Node.decEqArray cs ds with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h, _ => isFalse fun e => by cases e; exact h rfl
      | _, isFalse h => isFalse fun e => by cases e; exact h rfl
  | .const _, .var _ _ | .const _, .boundVar _ _ | .const _, .app _ _
  | .var _ _, .const _ | .var _ _, .boundVar _ _ | .var _ _, .app _ _
  | .boundVar _ _, .const _ | .boundVar _ _, .var _ _ | .boundVar _ _, .app _ _
  | .app _ _, .const _ | .app _ _, .var _ _ | .app _ _, .boundVar _ _ =>
      isFalse fun e => by cases e

def Op.decEq : (a b : Op) → Decidable (a = b)
  | .kind k, .kind l =>
      if h : k = l then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .indexed k is, .indexed l js =>
      if h : k = l ∧ is = js then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
      else isFalse fun e => by cases e; exact h ⟨rfl, rfl⟩
  | .node k f, .node l g =>
      if hk : k = l then
        match Node.decEq f g with
        | isTrue hf => isTrue (hk ▸ hf ▸ rfl)
        | isFalse hf => isFalse fun e => by cases e; exact hf rfl
      else isFalse fun e => by cases e; exact hk rfl
  | .kind _, .indexed _ _ | .kind _, .node _ _
  | .indexed _ _, .kind _ | .indexed _ _, .node _ _
  | .node _ _, .kind _ | .node _ _, .indexed _ _ =>
      isFalse fun e => by cases e

def Node.decEqArray : (a b : Array Node) → Decidable (a = b)
  | ⟨l⟩, ⟨m⟩ =>
      match Node.decEqList l m with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => by cases e; exact h rfl

def Node.decEqList : (a b : List Node) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      match Node.decEq x y, Node.decEqList xs ys with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h, _ => isFalse fun e => by cases e; exact h rfl
      | _, isFalse h => isFalse fun e => by cases e; exact h rfl
  | [], _ :: _ | _ :: _, [] => isFalse fun e => by cases e

end

instance : DecidableEq Node := Node.decEq
instance : DecidableEq Op := Op.decEq

end Telos
