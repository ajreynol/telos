import Telos.Preprocess.Pipeline
import Telos.Rewriter.Rewrite
import Telos.Preprocess.Theory.StringsStaticRewrite
import Telos.Preprocess.Theory.BVStaticRewrite
import Telos.Preprocess.Options

/-!
# The `static-rewrite` pass

cvc5's `StaticRewrite` pass (`src/preprocessing/passes/static_rewrite.cpp`): each
assertion is traversed bottom up, and each node is replaced by its theory's
`ppStaticRewrite` of it (`TheoryEngine::ppStaticRewrite`), whose result is
traversed again. The result is not rewritten (the `theory-preprocess` pass that
follows rewrites). Ported theory hooks:

* arithmetic equalities (`PreprocessRewriteEq::ppRewriteEq`): with
  `--arith-rewrite-equalities`, `(= a b)` becomes `(and (<= a b) (>= a b))`
  (`arith-eq-elim-int`/`-real`, then `aci_norm` for the order); otherwise
  normalized (`ArithRewriter::rewriteEqualityExt`; `Arith.normalizeEquality`);
* datatype equalities: `MACRO_DT_CONS_EQ` (`DatatypesRewriter.consEq`);
* `distinct`: blasted into disequalities (`TheoryBuiltin::ppStaticRewrite`,
  `distinct-elim`);
* string equalities: `rewriteStrEqualityExt`, in part
  (`Telos/Preprocess/Theory/StringsStaticRewrite.lean`);
* bit-vector equalities: `SolveEq` (`Telos/Preprocess/Theory/BVStaticRewrite.lean`).

Not ported: regular expression equalities (`RE_EQ_ELIM`).
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

/-- `PreprocessRewriteEq::ppRewriteEq` with `--arith-rewrite-equalities`:
`(= a b)` is `(and (<= a b) (>= a b))`. -/
def arithEqSplit (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let rule ← match a.typeHint, b.typeHint with
    | some .integer, some .integer => some Eo.CRule.arith_eq_elim_int
    | some .real, some .real => some Eo.CRule.arith_eq_elim_real
    | _, _ => none
  let r ← byRuleWithPremises rule [a, b] [] n
  let target := mkNode .AND #[mkNode .LEQ #[a, b], mkNode .GEQ #[a, b]]
  if r.1 == target then return r
  return r.trans (← checkBy .aci_norm r.1 target)

/-- The theory's `ppStaticRewrite` of a node. -/
def ppStaticRewrite (opts : PPOptions) (n : Node) (o : NodeOrder := {}) : Option (Rw n) :=
  match n.getKind with
  | .EQUAL =>
    match ppTheoryOf opts.termBased n with
    | .THEORY_ARITH => if opts.arithRewriteEq then arithEqSplit n else Arith.normalizeEquality n o
    | .THEORY_DATATYPES => DatatypesRewriter.consEq n
    | .THEORY_BV => bvStaticRewrite n
    | .THEORY_STRINGS => if n.getChildren[0]?.bind (·.typeHint) == some .string then strEqualityExt n else none
    | _ => none
  | .DISTINCT => blastDistinct n
  | _ => none

/-- `StaticRewrite::rewriteAssertion`: the children first, then the node, whose
static rewrite is traversed again (`fuel` bounds the repetitions). -/
def staticRewriteWith (opts : PPOptions) (o : NodeOrder := {}) : Nat → (n : Node) → Rw n
  | 0, n => Rw.id n
  | fuel + 1, n =>
    let r := rewriteChildren (m := Id) (fun c => staticRewriteWith opts o fuel c) n
    match ppStaticRewrite opts r.1 o with
    | some s => if s.1 == r.1 then r else (r.trans s).trans (staticRewriteWith opts o fuel s.1)
    | none => r

/-- The `static-rewrite` pass. -/
def Pipeline.staticRewrite {input : Node} (p : Pipeline input) (opts : PPOptions := {})
    (o : NodeOrder := {}) : Pipeline input :=
  Pipeline.mapAssertions p (staticRewriteWith opts o 1000)

end Telos.Preprocess
