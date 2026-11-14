import Telos.Theory.Common
import Telos.Rewriter.Rewriter

/-!
# The bit-vector rewriter

A port of cvc5's `TheoryBVRewriter` (`src/theory/bv/theory_bv_rewriter.cpp`),
kind by kind, following its rewrite table (`initializeRewrites`). Each of cvc5's
`RewriteRule<R>`s is the CPC RARE rule of the same name (`UgtEliminate` is
`bv-ugt-eliminate`, and a rule cvc5 implements in several cases has several RARE
rules, such as `bv-ult-zero-1` and `bv-ult-zero-2`), and its constant evaluation
(`EvalUlt`, …) is an `evaluate` step. As in cvc5, a `LinearRewriteStrategy` applies
its rules in sequence, each to the result of the previous, and `TRY_REWRITE`
returns the first rule that applies with `REWRITE_AGAIN_FULL`.

Not ported yet (the node is left as it is where cvc5 would apply them):

* the normalizations that cvc5 implements as macros over whole n-ary terms:
  `FlattenAssocCommut`, `AddCombineLikeTerms` and `MultSimplify` (for `bvadd`
  and `bvmul`; CPC certifies them with `bv_poly_norm`), `AndSimplify`,
  `OrSimplify` and `XorSimplify` (only their RARE instances `bv-*-simplify-*` are
  tried), `MultDistrib`, `MultDistribConst`, `NegAdd`,
  `NegMult`, `NegSub`, `NegIdemp`, `XorZero` and `BvComp`;
* the rules whose RARE versions telos cannot generate yet: `RepeatEliminate`,
  `BitwiseSlicing`, `UmuloEliminate`, `SmuloEliminate` (they use `:requires`);
* `IneqElimConversion`, which only applies to `ubv_to_int` comparisons.
-/

namespace Telos

namespace BvRewriter

open Node

/-- A step that may apply to a node. -/
abbrev Step := (m : Node) → Option (Rw m)

/-- One of cvc5's rewrite rules: the first of its RARE instances that applies. -/
def rules (names : List String) : Step := fun m =>
  firstOf (names.map fun name _ => byRule name m)

/-- cvc5's constant evaluation (`EvalUlt`, `EvalAdd`, …): the value of an
application to constants. -/
def evalConst : Step := fun m =>
  let cs := m.getChildren
  if !cs.isEmpty && cs.all (·.isConst) then byEvaluate m else none

/-- cvc5's `LinearRewriteStrategy`: each step, in order, applied to the result
of the previous one when it applies. -/
def linear (n : Node) (steps : List Step) : Rw n :=
  steps.foldl (fun r s => r.next s) (Rw.id n)

/-- The response for a rewrite, with status `changed` if it changed the node and
`unchanged` otherwise. -/
def respond {n : Node} (r : Rw n) (changed : RewriteStatus)
    (unchanged : RewriteStatus := .REWRITE_DONE) : RewriteResponse n :=
  ⟨if r.1 == n then unchanged else changed, r.1, r.2⟩

/-- cvc5's `TRY_REWRITE`: the first step that applies, with
`REWRITE_AGAIN_FULL`. -/
def tryRewrite (n : Node) (steps : List Step) : Option (RewriteResponse n) :=
  (firstOf (steps.map fun s _ => s n)).map fun ⟨m, h⟩ => ⟨.REWRITE_AGAIN_FULL, m, h⟩

/-- `Option.getD` for responses: `REWRITE_DONE` with the node unchanged. -/
def orDone {n : Node} : Option (RewriteResponse n) → RewriteResponse n
  | some r => r
  | none => .done n

/-! ## Rules of the core and of equality -/

/-- cvc5's `FailEq`: distinct constants are not equal (by evaluation). -/
def failEq : Step := fun m =>
  match m.getChildren with
  | #[.const (.bitVector ..), .const (.bitVector ..)] => byEvaluate m
  | _ => none

/-- cvc5's `ReflexivityEq`: orient an equality so that the smaller side comes
first. cvc5 compares node ids; telos uses its term order (`Node.lt`). -/
def reflexivityEq : Step := fun m =>
  match m.getChildren with
  | #[a, b] => if b.lt a then byRule "eq-symm" m else none
  | _ => none

/-- cvc5's `TheoryBVRewriter::RewriteEqual` (the same in pre- and
post-rewriting). -/
def rewriteEqual (n : Node) : RewriteResponse n :=
  respond (linear n [failEq, rules ["eq-refl"], reflexivityEq]) .REWRITE_DONE

/-- cvc5's `ConcatFlatten`: the children of nested `concat`s spliced in. Also
drops empty bit-vectors, which cvc5 does not have but CPC rules can produce
(`(@bv 0 0)`, the nil of `concat`). Certified by `aci_norm`. -/
def concatFlatten : Step := fun m =>
  let rec flat : Node → List Node
    | .app (.kind .BITVECTOR_CONCAT) cs => cs.toList.attach.flatMap fun ⟨c, _⟩ => flat c
    | .const (.bitVector 0 _) => []
    | c => [c]
  termination_by n => sizeOf n
  decreasing_by have := Array.sizeOf_lt_of_mem (Array.mem_def.2 ‹_›); simp_all; omega
  let cs := m.getChildren.toList.flatMap flat
  if cs == m.getChildren.toList then none
  else
    let r := match cs with
      | [c] => c
      | cs => mkNode .BITVECTOR_CONCAT cs.toArray
    checkBy .aci_norm m r

/-! ## The rewrite table -/

/-- The rules cvc5's `RewriteExtract` applies, before the final linear strategy. -/
def extractFirst (pre : Bool) (n : Node) : Option (RewriteResponse n) :=
  (tryRewrite n [rules ["bv-extract-concat-1", "bv-extract-concat-2", "bv-extract-concat-3",
      "bv-extract-concat-4"],
    rules ["bv-extract-sign-extend-1", "bv-extract-sign-extend-2", "bv-extract-sign-extend-3"],
    rules ["bv-extract-not"]]).orElse fun _ =>
  if pre then none else tryRewrite n [rules ["bv-extract-extract"]]

/-- cvc5's `BvIteConstCond`: `(bvite #b1 t e)` is `t` and `(bvite #b0 t e)` is
`e`, by evaluation. -/
def iteConstCond : Step := fun m =>
  match m.getChildren with
  | #[.const _, _, _] => byEvaluate m
  | _ => none

/-- cvc5's `RewriteITEBv`. -/
def rewriteIte (n : Node) : RewriteResponse n :=
  let r := linear n [evalConst, iteConstCond, rules ["bv-ite-equal-children"]]
  if r.1 != n then respond r .REWRITE_AGAIN else
  let r := linear n [rules ["bv-ite-const-children-1", "bv-ite-const-children-2"],
    rules ["bv-ite-equal-cond-1", "bv-ite-equal-cond-2", "bv-ite-equal-cond-3"]]
  if r.1 != n then respond r .REWRITE_AGAIN else
  respond (linear n [rules ["bv-ite-merge-then-if"], rules ["bv-ite-merge-else-if"],
    rules ["bv-ite-merge-then-else"], rules ["bv-ite-merge-else-else"]]) .REWRITE_AGAIN_FULL

/-- cvc5's `RewriteXor`. -/
def rewriteXor (pre : Bool) (n : Node) : RewriteResponse n :=
  orDone <| (tryRewrite n [evalConst, rules ["bv-xor-simplify-1", "bv-xor-simplify-2", "bv-xor-simplify-3"],
      rules ["bv-xor-concat-pullup", "bv-xor-concat-pullup2", "bv-xor-concat-pullup3"]]).orElse
    fun _ => if pre then none else tryRewrite n [rules ["bv-xor-ones"]]

/-- The rewrite of `n` by cvc5's rewrite table, in pre- or post-rewriting. -/
def rewriteNode (pre : Bool) (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .EQUAL => rewriteEqual n
  | .BITVECTOR_ULT =>
    respond (linear n [evalConst, rules ["bv-ult-self"], rules ["bv-ult-one"],
      rules ["bv-ult-ones"], rules ["bv-ult-zero-1", "bv-ult-zero-2"],
      rules ["bv-sign-extend-ult-const-1", "bv-sign-extend-ult-const-2",
        "bv-sign-extend-ult-const-3", "bv-sign-extend-ult-const-4"],
      rules ["bv-zero-extend-ult-const-1", "bv-zero-extend-ult-const-2"]]) .REWRITE_AGAIN_FULL
  | .BITVECTOR_ULTBV | .BITVECTOR_SLTBV => respond (linear n [evalConst]) .REWRITE_DONE
  | .BITVECTOR_SLT =>
    respond (linear n [evalConst, rules ["bv-lt-self"],
      rules ["bv-mult-slt-mult-1", "bv-mult-slt-mult-2"]]) .REWRITE_DONE
  | .BITVECTOR_ULE =>
    respond (linear n [evalConst, rules ["bv-ule-max"], rules ["bv-zero-ule"],
      rules ["bv-ule-zero"], rules ["bv-ule-self"], rules ["bv-ule-eliminate"]]) .REWRITE_AGAIN
  | .BITVECTOR_SLE =>
    respond (linear n [evalConst, rules ["bv-sle-eliminate"]]) .REWRITE_AGAIN
  | .BITVECTOR_UGT =>
    respond (linear n [rules ["bv-ugt-urem"], rules ["bv-ugt-eliminate"]]) .REWRITE_AGAIN .REWRITE_AGAIN
  | .BITVECTOR_SGT => respond (linear n [rules ["bv-sgt-eliminate"]]) .REWRITE_AGAIN .REWRITE_AGAIN
  | .BITVECTOR_UGE => respond (linear n [rules ["bv-uge-eliminate"]]) .REWRITE_AGAIN .REWRITE_AGAIN
  | .BITVECTOR_SGE =>
    respond (linear n [rules ["bv-sge-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_ITE => rewriteIte n
  | .BITVECTOR_NOT => respond (linear n [rules ["bv-not-idemp"], evalConst]) .REWRITE_DONE
  | .BITVECTOR_EXTRACT =>
    match extractFirst pre n with
    | some r => r
    | none =>
      respond (linear n [rules ["bv-extract-whole"], rules ["bv-extract-mult-leading-bit"],
        evalConst]) .REWRITE_AGAIN
  | .BITVECTOR_CONCAT =>
    orDone <| (tryRewrite n [concatFlatten, rules ["bv-concat-extract-merge"]]).orElse fun _ =>
      some (respond (linear n [rules ["bv-concat-merge-const"], evalConst]) .REWRITE_AGAIN)
  | .BITVECTOR_AND =>
    orDone <| tryRewrite n [rules ["bv-and-simplify-1", "bv-and-simplify-2"],
      rules ["bv-and-concat-pullup", "bv-and-concat-pullup2", "bv-and-concat-pullup3"], evalConst]
  | .BITVECTOR_OR =>
    orDone <| tryRewrite n [rules ["bv-or-simplify-1", "bv-or-simplify-2"],
      rules ["bv-or-concat-pullup", "bv-or-concat-pullup2", "bv-or-concat-pullup3"], evalConst]
  | .BITVECTOR_XOR => rewriteXor pre n
  | .BITVECTOR_XNOR =>
    respond (linear n [rules ["bv-xnor-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NAND =>
    respond (linear n [rules ["bv-nand-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NOR =>
    respond (linear n [rules ["bv-nor-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_COMP => respond (linear n [evalConst]) .REWRITE_DONE
  | .BITVECTOR_MULT =>
    orDone <| tryRewrite n (evalConst ::
      if pre then [] else [rules ["bv-mult-pow2-1", "bv-mult-pow2-2", "bv-mult-pow2-2b"]])
  | .BITVECTOR_ADD => if pre then .done n else orDone (tryRewrite n [evalConst])
  | .BITVECTOR_SUB =>
    respond (linear n [rules ["bv-sub-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NEG => respond (linear n [evalConst]) .REWRITE_AGAIN
  | .BITVECTOR_UDIV =>
    orDone <| (tryRewrite n [rules ["bv-udiv-pow2-not-one"]]).orElse fun _ =>
      some (respond (linear n [evalConst, rules ["bv-udiv-zero"], rules ["bv-udiv-one"]]) .REWRITE_DONE)
  | .BITVECTOR_UREM =>
    orDone <| (tryRewrite n [rules ["bv-urem-pow2-not-one"]]).orElse fun _ =>
      some (respond (linear n [evalConst, rules ["bv-urem-one"], rules ["bv-urem-self"]]) .REWRITE_DONE)
  | .BITVECTOR_SMOD =>
    respond (linear n [rules ["bv-smod-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_SDIV =>
    respond (linear n [rules ["bv-sdiv-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_SREM =>
    respond (linear n [rules ["bv-srem-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_SHL => shift n "shl"
  | .BITVECTOR_LSHR => shift n "lshr"
  | .BITVECTOR_ASHR => shift n "ashr"
  | .BITVECTOR_ZERO_EXTEND =>
    respond (linear n [rules ["bv-zero-extend-eliminate-0", "bv-zero-extend-eliminate"]])
      .REWRITE_AGAIN .REWRITE_AGAIN
  | .BITVECTOR_SIGN_EXTEND =>
    respond (linear n [rules ["bv-merge-sign-extend-1", "bv-merge-sign-extend-2"],
      rules ["bv-sign-extend-eliminate-0"], evalConst]) .REWRITE_AGAIN
  | .BITVECTOR_ROTATE_RIGHT =>
    respond (linear n [rules ["bv-rotate-right-eliminate-1", "bv-rotate-right-eliminate-2"]])
      .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_ROTATE_LEFT =>
    respond (linear n [rules ["bv-rotate-left-eliminate-1", "bv-rotate-left-eliminate-2"]])
      .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_REDOR =>
    respond (linear n [rules ["bv-redor-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_REDAND =>
    respond (linear n [rules ["bv-redand-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NEGO => respond (linear n [rules ["bv-nego-eliminate"]]) .REWRITE_AGAIN .REWRITE_AGAIN
  | .BITVECTOR_SDIVO => respond (linear n [rules ["bv-sdivo-eliminate"]]) .REWRITE_AGAIN .REWRITE_AGAIN
  | .BITVECTOR_UADDO | .BITVECTOR_SADDO | .BITVECTOR_UMULO | .BITVECTOR_SMULO
  | .BITVECTOR_USUBO | .BITVECTOR_SSUBO =>
    -- cvc5's `RewriteOverflow`: eliminated only when all children are constants.
    if n.getChildren.all (·.isConst) then
      orDone <| tryRewrite n [rules ["bv-uaddo-eliminate", "bv-saddo-eliminate", "bv-umulo-elim",
        "bv-smulo-elim", "bv-usubo-eliminate", "bv-ssubo-eliminate"]]
    else .done n
  | .BITVECTOR_SIZE => respond (linear n [byEvaluate]) .REWRITE_DONE
  | _ => .done n
where
  /-- cvc5's `RewriteShl`, `RewriteLshr` and `RewriteAshr`. -/
  shift (n : Node) (op : String) : RewriteResponse n :=
    orDone <| (tryRewrite n [rules [s!"bv-{op}-by-const-0", s!"bv-{op}-by-const-1",
        s!"bv-{op}-by-const-2"]]).orElse fun _ =>
      some (respond (linear n [evalConst, rules [s!"bv-{op}-zero"]]) .REWRITE_DONE)

end BvRewriter

/-- cvc5's `TheoryBVRewriter`. -/
def TheoryRewriter.bv : TheoryRewriter where
  preRewrite := BvRewriter.rewriteNode true
  postRewrite := BvRewriter.rewriteNode false

end Telos
