import Telos.Preprocess.Pipeline
import Telos.Rewriter.Rewrite

/-!
# The `static-rewrite` pass

cvc5's `StaticRewrite` pass (`src/preprocessing/passes/static_rewrite.cpp`): each
assertion is traversed bottom up, and each node is replaced by its theory's
`ppStaticRewrite` of it (`TheoryEngine::ppStaticRewrite`), whose result is
traversed again. The result is not rewritten (the `theory-preprocess` pass that
follows rewrites). Ported theory hooks:

* arithmetic equalities: normalized (`ArithRewriter::rewriteEqualityExt`, via
  `PreprocessRewriteEq::ppRewriteEq`; `Arith.normalizeEquality`);
* datatype equalities: `MACRO_DT_CONS_EQ` (`DatatypesRewriter.consEq`);
* `distinct`: blasted into disequalities (`TheoryBuiltin::ppStaticRewrite`,
  `distinct-elim`).

Not ported: bit-vector equalities (`SolveEq`), and string and regular expression
equalities (`rewriteEqualityExt`, `RE_EQ_ELIM`).
-/

namespace Telos.Preprocess

open Node

/-- `blastDistinct`: `(distinct t₁ … tₙ)` is the conjunction of the `(not (= tᵢ tⱼ))`,
for `i < j` (one disequality for two terms). -/
def blastDistinct (n : Node) : Option (Rw n) := do
  let ts := n.getChildren.toList
  let pairs := (List.range ts.length).flatMap fun i =>
    ((List.range ts.length).filter (i < ·)).map fun j => notNode (eqNode ts[i]! ts[j]!)
  let target := match pairs with
    | [d] => d
    | ds => mkNode .AND ds.toArray
  checkBy .distinct_elim n target

/-- The theory's `ppStaticRewrite` of a node. -/
def ppStaticRewrite (n : Node) : Option (Rw n) :=
  match n.getKind with
  | .EQUAL =>
    match theoryOf n with
    | .THEORY_ARITH => Arith.normalizeEquality n
    | .THEORY_DATATYPES => DatatypesRewriter.consEq n
    | _ => none
  | .DISTINCT => blastDistinct n
  | _ => none

/-- `StaticRewrite::rewriteAssertion`: the children first, then the node, whose
static rewrite is traversed again (`fuel` bounds the repetitions). -/
def staticRewriteWith : Nat → (n : Node) → Rw n
  | 0, n => Rw.id n
  | fuel + 1, n =>
    let r := rewriteChildren (m := Id) (fun c => staticRewriteWith fuel c) n
    match ppStaticRewrite r.1 with
    | some s => if s.1 == r.1 then r else (r.trans s).trans (staticRewriteWith fuel s.1)
    | none => r

/-- The `static-rewrite` pass. -/
def Pipeline.staticRewrite {input : Node} (p : Pipeline input) : Pipeline input :=
  Pipeline.mapAssertions p (staticRewriteWith 1000)

end Telos.Preprocess
