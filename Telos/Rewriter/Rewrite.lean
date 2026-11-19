import Telos.Rewriter.Theory.Bool
import Telos.Rewriter.Theory.Arith
import Telos.Rewriter.Theory.UF
import Telos.Rewriter.Theory.BV
import Telos.Rewriter.Theory.Arrays
import Telos.Rewriter.Theory.Strings
import Telos.Rewriter.Theory.Sets
import Telos.Rewriter.Theory.Datatypes
import Telos.Rewriter.Theory.Quantifiers

/-!
# The rewriter

`rewrite` is cvc5's `Rewriter::rewrite`: the driver (`rewriteWith`) with the
rewriter of each theory. Correctness is `Telos.rewrite_correct`
(`verification/TelosProofs/Rewriter/Rewriter.lean`).
-/

namespace Telos

/-- The rewriters of the theories other than arrays, with `strings` the strings
rewriter. -/
def baseTheoryRewriterWith (strings : TheoryRewriter) : TheoryId → TheoryRewriter
  | .THEORY_BOOL => .bool
  | .THEORY_ARITH => .arith
  | .THEORY_UF => .uf
  | .THEORY_BV => .bv
  | .THEORY_STRINGS => strings
  | .THEORY_SETS => .sets
  | .THEORY_DATATYPES => .datatypes
  | .THEORY_QUANTIFIERS => .quantifiers Rw.id
  | _ => .trivial

/-- The fuel for the rewrites the theory rewriters do as sub-steps: the
equality of two array indices, and the containments of strings. -/
def indexFuel : Nat := 1000

/-- The depth of the strings rewriter's use of the full rewriter (cvc5's
`StringsEntail::checkContains`, which rewrites `str.contains` terms, and so
may use `checkContains` again). At depth 0 it has none. -/
def stringsDepth : Nat := 3

/-- The rewriter of each theory, with the strings rewriter at depth `k`. The
arrays rewriter rewrites equalities of indices (cvc5's `mkEqNode`) with the
rewriters of the other theories: indices are not arrays here. -/
def theoryRewriterAt : Nat → TheoryId → TheoryRewriter
  | 0 => fun t => match t with
    | .THEORY_ARRAYS => .arrays (rewriteWith (baseTheoryRewriterWith (.strings Rw.id)) indexFuel)
    | .THEORY_QUANTIFIERS => .quantifiers (rewriteWith (baseTheoryRewriterWith (.strings Rw.id)) indexFuel)
    | t => baseTheoryRewriterWith (.strings Rw.id) t
  | k + 1 =>
    let strings := TheoryRewriter.strings (rewriteWith (theoryRewriterAt k) indexFuel)
    fun t => match t with
    | .THEORY_ARRAYS => .arrays (rewriteWith (baseTheoryRewriterWith strings) indexFuel)
    | .THEORY_QUANTIFIERS => .quantifiers (rewriteWith (baseTheoryRewriterWith strings) indexFuel)
    | t => baseTheoryRewriterWith strings t

/-- The rewriter of each theory. Theories not ported yet leave nodes unchanged. -/
def theoryRewriter : TheoryId → TheoryRewriter := theoryRewriterAt stringsDepth

/-- The fuel `rewrite` uses. It bounds the recursion depth of the driver. -/
def defaultFuel : Nat := 10000

/-- Rewrite a node to its normal form, with the certificate of the rewrite. -/
def rewriteCert (t : Node) : Rw t := rewriteWith theoryRewriter defaultFuel t

/-- `rewriteCert` with a rewrite cache kept between calls, as cvc5's rewriter
keeps its cache: the rewrite, and the cache after it. -/
def rewriteCertCached (c : Cache) (t : Node) : Rw t × Cache :=
  (rewriteWithM theoryRewriter defaultFuel t).run c

/-- cvc5's `Rewriter::rewrite`: rewrite a node to its normal form. -/
def rewrite (t : Node) : Node := (rewriteCert t).1

end Telos
