import Std.Data.HashMap
import Telos.Core.Node.Node

/-!
# Nodes as hash-map keys

`Key` wraps a node for the maps and sets of the rewriter and the preprocessor:
it hashes by the node's stored hash (`Node.hash`) and compares with
`Node.decEq`, both constant time on shared subterms.
-/

namespace Telos

/-- A node as a hash-map key. -/
structure Key where
  node : Node

instance : BEq Key := ⟨fun a b => a.node == b.node⟩
instance : Hashable Key := ⟨fun k => k.node.hash⟩

instance : LawfulBEq Key where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, decide_eq_true_eq] at h
    rw [h]
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable Key where
  hash_eq {a b} h := by rw [eq_of_beq h]

/-- A theory's internal fact `conc`, from the inference `id` with the premises
`exp`, added to its derivations (newest first): a fact may be derived again,
after a backtrack, from other premises, and the proof builder takes the
derivation whose premises are the reason of the edge it proves. -/
def addFact (m : Std.HashMap Key (List (String × Node))) (conc : Node) (id : String) (exp : Node) :
    Std.HashMap Key (List (String × Node)) :=
  let l := m.getD ⟨conc⟩ []
  if l.any (·.2 == exp) then m else m.insert ⟨conc⟩ ((id, exp) :: l)

end Telos
