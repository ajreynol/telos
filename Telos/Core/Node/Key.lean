import Telos.Core.Node.Node

/-!
# Nodes as hash-map keys

The derived `Hashable Node` hashes the whole tree, so a cache keyed by nodes
pays a traversal of each node on every lookup, which on deep terms dominates.
`Key` hashes only the top of a node (`shallowHash`); equality is still
structural, so a map keyed by `Key` behaves as one keyed by `Node`.
-/

namespace Telos

/-- A hash of the top of a node, to depth `d`. -/
def shallowHash : Nat → Node → UInt64
  | 0, _ => 7
  | _, .const c => hash c
  | _, .var n _ | _, .boundVar n _ => hash n
  | _, .skolem id _ => hash id
  | d + 1, .app op cs =>
    let h := mixHash (hash op.getKind) (hash cs.size)
    cs.attach.foldl (fun h ⟨c, _⟩ => mixHash h (shallowHash d c)) h

/-- A node, hashed by its top (`shallowHash`), compared structurally. -/
structure Key where
  node : Node

instance : BEq Key := ⟨fun a b => a.node == b.node⟩
instance : Hashable Key := ⟨fun k => shallowHash 6 k.node⟩

end Telos
