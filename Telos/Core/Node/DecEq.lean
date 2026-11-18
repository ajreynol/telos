import Telos.Core.Node.Node

/-!
# Decidable equality of nodes

`Node.decEq` (in `Telos/Core/Node/Node.lean`, where the specification files can
use it) decides structural equality, in constant time for nodes that are the
same in memory or whose hashes differ. This module is kept for its importers.
-/
