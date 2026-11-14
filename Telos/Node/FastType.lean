import Telos.Node.ToEo

/-!
# Fast types, for strategies

`Node.typeHint` is the type of a node, computed structurally for the common
operators, and by Logos's type checker (`Node.getType`) otherwise. It agrees
with `getType` on well-typed nodes of the theories telos supports, and is much
cheaper: it does not translate the node.

It is only for strategy decisions (which rewrite to try, such as `isInt` in the
arithmetic rewriter, and `theoryOf`). Nothing that is proved depends on it: a
wrong answer can only make telos miss a rewrite or differ from cvc5, since every
step is still justified by a check or a theorem that does not use it.
-/

namespace Telos.Node

def typeHint : Node → Option TypeNode
  | .const (.boolean _) => some .boolean
  | .const (.integer _) => some .integer
  | .const (.rational _) => some .real
  | .var _ T | .boundVar _ T => some T
  | .app (.kind .ADD) ⟨c :: _⟩ | .app (.kind .MULT) ⟨c :: _⟩ | .app (.kind .SUB) ⟨c :: _⟩
  | .app (.kind .NEG) ⟨c :: _⟩ | .app (.kind .ABS) ⟨c :: _⟩ => typeHint c
  | n@(.app (.kind k) _) =>
    match k with
    | .DIVISION | .DIVISION_TOTAL | .TO_REAL => some .real
    | .INTS_DIVISION | .INTS_MODULUS | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL
    | .TO_INTEGER => some .integer
    | .EQUAL | .NOT | .AND | .OR | .IMPLIES | .XOR | .LT | .LEQ | .GT | .GEQ
    | .IS_INTEGER | .FORALL | .EXISTS => some .boolean
    | _ => n.getType
  | n => n.getType
termination_by n => sizeOf n
decreasing_by all_goals (simp_all; omega)

end Telos.Node
