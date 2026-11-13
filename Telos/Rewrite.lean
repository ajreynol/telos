import Telos.Theory.Bool

/-!
# The rewriter

`rewrite` is cvc5's `Rewriter::rewrite`: the driver (`rewriteWith`) with the
rewriter of each theory. Correctness is `Telos.rewrite_correct`
(`verification/TelosProofs/Rewriter.lean`).
-/

namespace Telos

/-- The rewriter of each theory. Theories not ported yet leave nodes unchanged. -/
def theoryRewriter : TheoryId → TheoryRewriter
  | .THEORY_BOOL => .bool
  | _ => .trivial

/-- The fuel `rewrite` uses. It bounds the recursion depth of the driver. -/
def defaultFuel : Nat := 10000

/-- Rewrite a node to its normal form, with the certificate of the rewrite. -/
def rewriteCert (t : Node) : Rw t := rewriteWith theoryRewriter defaultFuel t

/-- cvc5's `Rewriter::rewrite`: rewrite a node to its normal form. -/
def rewrite (t : Node) : Node := (rewriteCert t).1

end Telos
