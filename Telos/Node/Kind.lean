/-!
# Node kinds

A copy of cvc5's internal `Kind` enumeration (`src/expr/kind_template.h`,
generated from the theories' `kinds` files). The constructor names are cvc5's, so
code ported from cvc5's rewriters reads the same.

Only kinds that `Node.toEo` (`Telos/Node/ToEo.lean`) gives a semantics to are
listed. When you add a kind, add its `toEo` case in the same change. A kind with no
`toEo` case translates to `Term.Stuck`, so no node of that kind is well typed.
-/

namespace Telos

inductive Kind where
  -- Constants (cvc5 `CONST_*` kinds; the payload is in `Const`).
  | CONST_BOOLEAN
  | CONST_INTEGER
  | CONST_RATIONAL
  | CONST_BITVECTOR
  | CONST_STRING
  -- Variables (cvc5 `VARIABLE`, for user-declared constants and functions, and
  -- `BOUND_VARIABLE`).
  | VARIABLE
  | BOUND_VARIABLE
  -- theory/builtin
  | EQUAL
  -- theory/booleans
  | NOT
  | AND
  | IMPLIES
  | OR
  | XOR
  | ITE
  -- theory/arith
  | ADD
  | SUB
  | NEG
  | MULT
  | DIVISION
  | INTS_DIVISION
  | INTS_MODULUS
  | DIVISION_TOTAL
  | INTS_DIVISION_TOTAL
  | INTS_MODULUS_TOTAL
  | ABS
  | LT
  | LEQ
  | GT
  | GEQ
  | TO_REAL
  | TO_INTEGER
  | IS_INTEGER
  -- theory/bv (parameterized kinds take their indices from `Op.indexed`)
  | BITVECTOR_EXTRACT
  -- theory/uf (the function is the operator: `Op.node APPLY_UF f`)
  | APPLY_UF
  | DISTINCT
  -- theory/quantifiers
  | FORALL
  | EXISTS
  | BOUND_VAR_LIST
  /-- Instantiation patterns. They carry no semantics, and `toEo` drops them. -/
  | INST_PATTERN_LIST
  deriving DecidableEq, Repr, Inhabited, Hashable, Ord

/-- cvc5's `TheoryId` (`src/theory/theory_id.h`), for the theories `Kind` covers. -/
inductive TheoryId where
  | THEORY_BUILTIN
  | THEORY_BOOL
  | THEORY_ARITH
  | THEORY_BV
  | THEORY_UF
  | THEORY_ARRAYS
  | THEORY_SETS
  | THEORY_STRINGS
  | THEORY_QUANTIFIERS
  deriving DecidableEq, Repr, Inhabited

/-- cvc5's `kindToTheoryId`: the theory that owns a kind, and whose rewriter
rewrites nodes of that kind. -/
def Kind.theoryId : Kind → TheoryId
  | .CONST_BOOLEAN => .THEORY_BOOL
  | .CONST_INTEGER | .CONST_RATIONAL => .THEORY_ARITH
  | .CONST_BITVECTOR => .THEORY_BV
  | .CONST_STRING => .THEORY_STRINGS
  | .VARIABLE | .BOUND_VARIABLE | .EQUAL => .THEORY_BUILTIN
  | .NOT | .AND | .IMPLIES | .OR | .XOR | .ITE => .THEORY_BOOL
  | .ADD | .SUB | .NEG | .MULT | .DIVISION | .INTS_DIVISION | .INTS_MODULUS | .ABS
  | .DIVISION_TOTAL | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL
  | .LT | .LEQ | .GT | .GEQ | .TO_REAL | .TO_INTEGER | .IS_INTEGER => .THEORY_ARITH
  | .BITVECTOR_EXTRACT => .THEORY_BV
  | .APPLY_UF | .DISTINCT => .THEORY_UF
  | .FORALL | .EXISTS | .BOUND_VAR_LIST | .INST_PATTERN_LIST => .THEORY_QUANTIFIERS

/-- The quantifier kinds, whose congruence is in their body only. -/
def Kind.isQuantifier : Kind → Bool
  | .FORALL | .EXISTS => true
  | _ => false

end Telos
