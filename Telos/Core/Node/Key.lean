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

end Telos
