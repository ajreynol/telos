import Telos.Theory.Bool
import Telos.Theory.Arith
import Telos.Theory.UF
import Telos.Theory.BV
import Telos.Theory.Arrays

/-!
# The rewriter

`rewrite` is cvc5's `Rewriter::rewrite`: the driver (`rewriteWith`) with the
rewriter of each theory. Correctness is `Telos.rewrite_correct`
(`verification/TelosProofs/Rewriter.lean`).
-/

namespace Telos

/-- The rewriters of the theories other than arrays. -/
def baseTheoryRewriter : TheoryId → TheoryRewriter
  | .THEORY_BOOL => .bool
  | .THEORY_ARITH => .arith
  | .THEORY_UF => .uf
  | .THEORY_BV => .bv
  | _ => .trivial

/-- The fuel for rewriting the equality of two array indices. -/
def indexFuel : Nat := 1000

/-- The rewriter of each theory. Theories not ported yet leave nodes unchanged.
The arrays rewriter rewrites equalities of indices (cvc5's `mkEqNode`) with the
rewriters of the other theories: indices are not arrays here. -/
def theoryRewriter : TheoryId → TheoryRewriter
  | .THEORY_ARRAYS => .arrays (rewriteWith baseTheoryRewriter indexFuel)
  | t => baseTheoryRewriter t

/-- The fuel `rewrite` uses. It bounds the recursion depth of the driver. -/
def defaultFuel : Nat := 10000

/-- Rewrite a node to its normal form, with the certificate of the rewrite. -/
def rewriteCert (t : Node) : Rw t := rewriteWith theoryRewriter defaultFuel t

/-- cvc5's `Rewriter::rewrite`: rewrite a node to its normal form. -/
def rewrite (t : Node) : Node := (rewriteCert t).1

end Telos
