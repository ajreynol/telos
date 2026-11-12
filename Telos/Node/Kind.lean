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
  -- Free constants (cvc5 `VARIABLE`; user-declared constants and functions).
  | VARIABLE
  -- theory/builtin
  | EQUAL
  -- theory/booleans
  | NOT
  | AND
  | IMPLIES
  | OR
  | XOR
  | ITE
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- cvc5's `TheoryId` (`src/theory/theory_id.h`), for the theories `Kind` covers. -/
inductive TheoryId where
  | THEORY_BUILTIN
  | THEORY_BOOL
  | THEORY_ARITH
  | THEORY_BV
  deriving DecidableEq, Repr, Inhabited

/-- cvc5's `kindToTheoryId`: the theory that owns a kind, and whose rewriter
rewrites nodes of that kind. -/
def Kind.theoryId : Kind → TheoryId
  | .CONST_BOOLEAN => .THEORY_BOOL
  | .CONST_INTEGER | .CONST_RATIONAL => .THEORY_ARITH
  | .CONST_BITVECTOR => .THEORY_BV
  | .VARIABLE | .EQUAL => .THEORY_BUILTIN
  | .NOT | .AND | .IMPLIES | .OR | .XOR | .ITE => .THEORY_BOOL

end Telos
