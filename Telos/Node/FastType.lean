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

/-- The width of a bit-vector type. -/
def bvWidth? : Option TypeNode → Option Int
  | some (.bitVector w) => some w
  | _ => none

/-- The type of a set operator's application, from the type of its first
child. -/
def setTypeOfFirst : Kind → Option TypeNode → Option TypeNode
  | .SET_UNION, T | .SET_INTER, T | .SET_MINUS, T => T
  | .SET_SINGLETON, some T | .SET_INSERT, some T => some (.set T)
  | .SET_CHOOSE, some (.set T) => some T
  | _, _ => none

-- The match over `Kind` is large; its compilation needs more than the default.
set_option maxHeartbeats 1000000 in
def typeHint : Node → Option TypeNode
  | .const (.boolean _) => some .boolean
  | .const (.integer _) => some .integer
  | .const (.rational _) => some .real
  | .const (.bitVector w _) => some (.bitVector w)
  | .const (.emptySet T) => some (.set T)
  | .var _ T | .boundVar _ T => some T
  | .app (.kind .ADD) ⟨c :: _⟩ | .app (.kind .MULT) ⟨c :: _⟩ | .app (.kind .SUB) ⟨c :: _⟩
  | .app (.kind .NEG) ⟨c :: _⟩ | .app (.kind .ABS) ⟨c :: _⟩ => typeHint c
  | .app (.kind .ITE) ⟨[_, t, _]⟩ | .app (.kind .BITVECTOR_ITE) ⟨[_, t, _]⟩ => typeHint t
  | .app (.kind .SELECT) ⟨a :: _⟩ =>
    match typeHint a with
    | some (.array _ e) => some e
    | _ => none
  | .app (.kind .STORE) ⟨a :: _⟩ => typeHint a
  | .app (.kind .BITVECTOR_CONCAT) cs => do
    let ws ← cs.attach.toList.mapM fun ⟨c, _⟩ => bvWidth? (typeHint c)
    return .bitVector ws.sum
  | n@(.app (.indexed k is) cs) =>
    match k, is.toList, h : cs.toList with
    | .BITVECTOR_EXTRACT, [i, j], _ => some (.bitVector (i - j + 1))
    | .INT_TO_BITVECTOR, [w], _ => some (.bitVector w)
    | .BITVECTOR_ZERO_EXTEND, [k], [c] | .BITVECTOR_SIGN_EXTEND, [k], [c] =>
      have : c ∈ cs := by rw [Array.mem_def, h]; simp
      (bvWidth? (typeHint c)).map fun w => .bitVector (w + k)
    | .BITVECTOR_REPEAT, [k], [c] =>
      have : c ∈ cs := by rw [Array.mem_def, h]; simp
      (bvWidth? (typeHint c)).map fun w => .bitVector (w * k)
    | .BITVECTOR_ROTATE_LEFT, _, [c] | .BITVECTOR_ROTATE_RIGHT, _, [c] =>
      have : c ∈ cs := by rw [Array.mem_def, h]; simp
      typeHint c
    | _, _, _ => n.getType
  | n@(.app (.kind k) cs) =>
    match k with
    | .DIVISION | .DIVISION_TOTAL | .TO_REAL => some .real
    | .INTS_DIVISION | .INTS_MODULUS | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL
    | .TO_INTEGER | .BITVECTOR_SIZE | .BITVECTOR_UBV_TO_INT | .BITVECTOR_SBV_TO_INT
    | .STRING_LENGTH | .STRING_INDEXOF | .STRING_INDEXOF_RE | .STRING_STOI
    | .STRING_TO_CODE => some .integer
    | .STRING_SUBSTR | .STRING_CHARAT | .STRING_REPLACE | .STRING_REPLACE_ALL | .STRING_REPLACE_RE
    | .STRING_REPLACE_RE_ALL | .STRING_UPDATE | .STRING_REV | .STRING_TO_LOWER
    | .STRING_TO_UPPER | .STRING_ITOS | .STRING_FROM_CODE | .STRING_CONCAT => some .string
    | .EQUAL | .NOT | .AND | .OR | .IMPLIES | .XOR | .LT | .LEQ | .GT | .GEQ
    | .IS_INTEGER | .FORALL | .EXISTS | .DISTINCT
    | .BITVECTOR_ULT | .BITVECTOR_ULE | .BITVECTOR_UGT | .BITVECTOR_UGE
    | .BITVECTOR_SLT | .BITVECTOR_SLE | .BITVECTOR_SGT | .BITVECTOR_SGE
    | .BITVECTOR_UADDO | .BITVECTOR_SADDO | .BITVECTOR_UMULO | .BITVECTOR_SMULO
    | .BITVECTOR_USUBO | .BITVECTOR_SSUBO | .BITVECTOR_SDIVO | .BITVECTOR_NEGO
    | .STRING_CONTAINS | .STRING_PREFIX | .STRING_SUFFIX | .STRING_IN_REGEXP | .STRING_LT
    | .STRING_LEQ | .STRING_IS_DIGIT | .SET_MEMBER | .SET_SUBSET | .SET_IS_EMPTY
    | .SET_IS_SINGLETON => some .boolean
    | .BITVECTOR_COMP | .BITVECTOR_REDOR | .BITVECTOR_REDAND | .BITVECTOR_ULTBV
    | .BITVECTOR_SLTBV => some (.bitVector 1)
    | .BITVECTOR_AND | .BITVECTOR_OR | .BITVECTOR_XOR | .BITVECTOR_ADD | .BITVECTOR_MULT
    | .BITVECTOR_NOT | .BITVECTOR_NEG | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR
    | .BITVECTOR_SUB | .BITVECTOR_UDIV | .BITVECTOR_UREM | .BITVECTOR_SDIV | .BITVECTOR_SREM
    | .BITVECTOR_SMOD | .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR =>
      match h : cs.toList with
      | c :: _ =>
        have : c ∈ cs := by rw [Array.mem_def, h]; simp
        typeHint c
      | [] => n.getType
    | .SET_UNION | .SET_INTER | .SET_MINUS | .SET_SINGLETON | .SET_CHOOSE | .SET_INSERT =>
      match h : cs.toList with
      | c :: _ =>
        have : c ∈ cs := by rw [Array.mem_def, h]; simp
        setTypeOfFirst k (typeHint c)
      | [] => n.getType
    | _ => n.getType
  | n => n.getType
termination_by n => sizeOf n
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (simp_all; omega)

end Telos.Node
