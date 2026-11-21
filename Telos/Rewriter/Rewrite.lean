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
rewriter and `o` the order of node ids (`NodeOrder`). -/
def baseTheoryRewriterWith (strings : TheoryRewriter) (o : NodeOrder := {}) : TheoryId → TheoryRewriter
  | .THEORY_BOOL => .bool
  | .THEORY_ARITH => .arith o
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
def theoryRewriterAt (o : NodeOrder := {}) : Nat → TheoryId → TheoryRewriter
  | 0 => fun t => match t with
    | .THEORY_ARRAYS => .arrays (rewriteWith (baseTheoryRewriterWith (.strings Rw.id) o) indexFuel)
    | .THEORY_QUANTIFIERS => .quantifiers (rewriteWith (baseTheoryRewriterWith (.strings Rw.id) o) indexFuel)
    | t => baseTheoryRewriterWith (.strings Rw.id) o t
  | k + 1 =>
    let strings := TheoryRewriter.strings (rewriteWith (theoryRewriterAt o k) indexFuel)
    fun t => match t with
    | .THEORY_ARRAYS => .arrays (rewriteWith (baseTheoryRewriterWith strings o) indexFuel)
    | .THEORY_QUANTIFIERS => .quantifiers (rewriteWith (baseTheoryRewriterWith strings o) indexFuel)
    | t => baseTheoryRewriterWith strings o t

/-- The rewriter of each theory, with the order of node ids `o`. Theories not
ported yet leave nodes unchanged. -/
def theoryRewriterOf (o : NodeOrder) : TheoryId → TheoryRewriter := theoryRewriterAt o stringsDepth

/-- The rewriter of each theory, with the structural order. -/
def theoryRewriter : TheoryId → TheoryRewriter := theoryRewriterOf {}

/-- The fuel `rewrite` uses. It bounds the recursion depth of the driver. -/
def defaultFuel : Nat := 10000

/-- Rewrite a node to its normal form, with the certificate of the rewrite. -/
def rewriteCert (t : Node) (o : NodeOrder := {}) : Rw t := rewriteWith (theoryRewriterOf o) defaultFuel t

/-- `rewriteCert` with a rewrite cache kept between calls, as cvc5's rewriter
keeps its cache: the rewrite, and the cache after it. -/
def rewriteCertCached (c : Cache) (t : Node) (o : NodeOrder := {}) : Rw t × Cache :=
  (rewriteWithM (theoryRewriterOf o) defaultFuel t).run c

/-- cvc5's `Rewriter::rewrite`: rewrite a node to its normal form. -/
def rewrite (t : Node) (o : NodeOrder := {}) : Node := (rewriteCert t o).1

end Telos
