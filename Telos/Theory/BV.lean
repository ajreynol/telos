import Telos.Theory.Common
import Telos.Theory.BVNorm
import Telos.Rules.Programs
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

The normalizations over whole n-ary terms are in `Telos/Theory/BVNorm.lean`.

Not ported yet (the node is left as it is where cvc5 would apply them):

* `NegMult` (see `BVNorm.lean`) and `BvComp`.
-/

namespace Telos

namespace BvRewriter

open Node BvNorm

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

/-- A rule whose argument is the equation `(= n m)` and whose `:requires` computes
`m` with a Logos program (`bv-repeat-elim`, `bv-bitwise-slicing`): `m` is
computed by that program, read back, and validated by the rule. -/
def byProgram (r : Eo.CRule) (compute : Eo.Term → Eo.Term) : Step := fun m =>
  Node.ofEo m.vars (compute m.toEo) >>= fun k => if k == m then none else checkBy r m k

/-- cvc5's `RepeatEliminate`, by `bv-repeat-elim`. -/
def repeatEliminate : Step :=
  byProgram .bv_repeat_elim fun
    | .Apply (.UOp1 .repeat n) a =>
      Eo.__eo_list_singleton_elim (.UOp .concat) (Eo.__eo_list_repeat (.UOp .concat) a n)
    | _ => .Stuck

/-- cvc5's `BitwiseSlicing`, by `bv-bitwise-slicing`: it applies when the first
constant child is neither zero nor all ones, and the width is not 1. -/
def bitwiseSlicing : Step := fun m =>
  let first := m.getChildren.findSome? fun c => match c with
    | .const (.bitVector w v) => some (w, v)
    | _ => none
  match first with
  | some (w, v) =>
    if w > 1 && v != 0 && v != 2 ^ w.toNat - 1 then
      byProgram .bv_bitwise_slicing Eo.__bv_mk_bitwise_slicing m
    else none
  | none => none

/-- cvc5's `IneqElimConversion`: a comparison of `int_to_bv` terms and constants
is a comparison of integers, by `uf-int2bv-bvult-equiv` (`bvule`: `-bvule-`).
The UF rewriter then turns `(ubv_to_int ((_ int_to_bv w) t))` into
`(mod_total t 2^w)`. -/
def ineqElimConversion : Step := fun m =>
  let cs := m.getChildren
  if cs.all (fun c => c.getKind == .INT_TO_BITVECTOR || c.isConst) && !cs.all (·.isConst) then
    rules (if m.getKind == .BITVECTOR_ULT then ["uf-int2bv-bvult-equiv"] else ["uf-int2bv-bvule-equiv"]) m
  else none

/-- cvc5's `UltOnes` with the all-ones constant on the left: `(bvult ones x)` is
`false`. CPC has no rule for it, so it is derived: `bv-ule-max` gives
`(= (bvule x ones) true)` and `bv-ule-eliminate` gives
`(= (bvule x ones) (not (bvult ones x)))`; then `symm`, `trans`, `true_elim` and
`false_intro`. The rules write `ones` as `((_ int_to_bv w) (2^w - 1))`, so the
literal is first written that way (`toSymbolic`). -/
def ultOnesLeft : Step := fun m =>
  match m.getChildren with
  | #[c@(.const (.bitVector w v)), x] =>
    if w ≥ 1 && v == 2 ^ w.toNat - 1 then do
      let ones := Node.app (.indexed .INT_TO_BITVECTOR #[w]) #[.const (.integer v)]
      let m' := mkNode .BITVECTOR_ULT #[ones, x]
      let size := mkNode .BITVECTOR_SIZE #[x]
      let maxE := mkNode .SUB #[mkNode .POW2 #[size], .const (.integer 1)]
      let cmds : List Eo.CCmd := [
        .step .evaluate (toArgList [size.toEo]) .nil,
        .step .symm .nil (.cons 0 .nil),
        .step .evaluate (toArgList [maxE.toEo]) .nil,
        .step .symm .nil (.cons 0 .nil),
        .step .bv_ule_max (toArgList [x.toEo, Eo.Term.Numeral v, Eo.Term.Numeral w]) (.cons 2 (.cons 0 .nil)),
        .step .bv_ule_eliminate (toArgList [x.toEo, ones.toEo]) .nil,
        .step .symm .nil (.cons 0 .nil),
        .step .trans .nil (.cons 0 (.cons 2 .nil)),
        .step .true_elim .nil (.cons 0 .nil),
        .step .false_intro .nil (.cons 0 .nil)]
      let r ← toSymbolic m m'
      let _ := c
      r.next? (applyCmds (cmds.foldr .cons .nil))
    else none
  | _ => none

/-- cvc5's `AndOrXorConcatPullUp` applies when the first `concat` child has a
constant, and its first constant is zero, one or all ones. -/
def pullUpApplies (m : Node) : Bool :=
  match m.getChildren.find? (·.getKind == .BITVECTOR_CONCAT) with
  | some c =>
    match c.getChildren.findSome? fun d => match d with
        | .const (.bitVector w v) => some (w, v)
        | _ => none with
    | some (w, v) => v == 0 || v == 1 || v == 2 ^ w.toNat - 1
    | none => false
  | none => false

/-- cvc5's `AndOrXorConcatPullUp`, by the RARE rules `bv-<op>-concat-pullup*`. -/
def concatPullUp (op : String) : Step := fun m =>
  if pullUpApplies m then
    rules [s!"bv-{op}-concat-pullup", s!"bv-{op}-concat-pullup2", s!"bv-{op}-concat-pullup3"] m
  else none

/-! ## The rewrite table -/

/-- The rules cvc5's `RewriteExtract` applies, before the final linear strategy. -/
def extractFirst (pre : Bool) (n : Node) : Option (RewriteResponse n) :=
  (tryRewrite n [rules ["bv-extract-concat-1", "bv-extract-concat-2", "bv-extract-concat-3",
      "bv-extract-concat-4"],
    rules ["bv-extract-sign-extend-1", "bv-extract-sign-extend-2", "bv-extract-sign-extend-3"],
    rules ["bv-extract-not"]]).orElse fun _ =>
  if pre then none else tryRewrite n [rules ["bv-extract-extract"]]

/-- cvc5's `BvIteConstCond`: `(bvite #b1 t e)` is `t` and `(bvite #b0 t e)` is
`e` (`bv-ite-const-cond-1/2`; cvc5 itself proves this step with a trust step). -/
def iteConstCond : Step := rules ["bv-ite-const-cond-1", "bv-ite-const-cond-2"]

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
  orDone <| (tryRewrite n [evalConst, bitwiseStep xorSimplify, bitwiseStep xorZero,
      concatPullUp "xor"]).orElse
    fun _ => if pre then none else tryRewrite n [rules ["bv-xor-ones"], bitwiseSlicing]

/-- The rewrite of `n` by cvc5's rewrite table, in pre- or post-rewriting. -/
def rewriteNode (pre : Bool) (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .EQUAL => rewriteEqual n
  | .BITVECTOR_ULT =>
    respond (linear n [evalConst, rules ["bv-ult-self"], rules ["bv-ult-one"],
      rules ["bv-ult-ones"], ultOnesLeft, rules ["bv-ult-zero-1", "bv-ult-zero-2"],
      -- cvc5 tries the most significant bit case first (`-2` and `-4`).
      rules ["bv-sign-extend-ult-const-2", "bv-sign-extend-ult-const-1",
        "bv-sign-extend-ult-const-4", "bv-sign-extend-ult-const-3"],
      rules ["bv-zero-extend-ult-const-1", "bv-zero-extend-ult-const-2"],
      ineqElimConversion]) .REWRITE_AGAIN_FULL
  | .BITVECTOR_ULTBV | .BITVECTOR_SLTBV => respond (linear n [evalConst]) .REWRITE_DONE
  | .BITVECTOR_SLT =>
    respond (linear n [evalConst, rules ["bv-lt-self"],
      rules ["bv-mult-slt-mult-1", "bv-mult-slt-mult-2"]]) .REWRITE_DONE
  | .BITVECTOR_ULE =>
    respond (linear n [evalConst, rules ["bv-ule-max"], rules ["bv-zero-ule"],
      ineqElimConversion, rules ["bv-ule-zero"], rules ["bv-ule-self"],
      rules ["bv-ule-eliminate"]]) .REWRITE_AGAIN
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
    orDone <| tryRewrite n ([evalConst, bitwiseStep (andOrSimplify true),
      concatPullUp "and"] ++
      if pre then [] else [bitwiseSlicing])
  | .BITVECTOR_OR =>
    orDone <| tryRewrite n ([evalConst, bitwiseStep (andOrSimplify false),
      concatPullUp "or"] ++
      if pre then [] else [bitwiseSlicing])
  | .BITVECTOR_XOR => rewriteXor pre n
  | .BITVECTOR_XNOR =>
    respond (linear n [rules ["bv-xnor-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NAND =>
    respond (linear n [rules ["bv-nand-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NOR =>
    respond (linear n [rules ["bv-nor-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_COMP =>
    -- cvc5's `EvalComp`: Logos's `evaluate` does not reduce `bvcomp`, so a
    -- constant one is eliminated by `bv-comp-eliminate` to
    -- `(ite (= a b) #b1 #b0)`, which the equality and Boolean rewriters reduce.
    if n.getChildren.all (·.isConst) then
      respond (linear n [rules ["bv-comp-eliminate"]]) .REWRITE_AGAIN_FULL
    else .done n
  | .BITVECTOR_MULT =>
    orDone <| tryRewrite n ([polyStep flattenAssocCommut, polyStep multSimplify] ++
      if pre then [] else [rules ["bv-mult-pow2-1", "bv-mult-pow2-2", "bv-mult-pow2-2b"],
        polyStep multDistribConst, polyStep multDistrib])
  | .BITVECTOR_ADD =>
    if pre then respond (linear n [polyStep flattenAssocCommut]) .REWRITE_DONE
    else respond (linear n [polyStep flattenAssocCommut, polyStep addCombineLikeTerms])
      .REWRITE_AGAIN_FULL
  | .BITVECTOR_SUB =>
    respond (linear n [rules ["bv-sub-eliminate"]]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
  | .BITVECTOR_NEG =>
    -- As in cvc5, `NegAdd` is tested on the original node.
    match polyStep negAdd n with
    | some ⟨m, h⟩ => ⟨.REWRITE_AGAIN_FULL, m, h⟩
    | none => respond (linear n [evalConst, polyStep negIdemp, polyStep negSub]) .REWRITE_AGAIN
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
  | .BITVECTOR_REPEAT =>
    respond (linear n [repeatEliminate]) .REWRITE_AGAIN_FULL .REWRITE_AGAIN_FULL
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
      orDone <| tryRewrite n [rules ["bv-uaddo-eliminate", "bv-saddo-eliminate",
        "bv-usubo-eliminate", "bv-ssubo-eliminate"],
        byProgram .bv_umulo_elim (fun
          | .Apply (.Apply (.UOp .bvumulo) a) b => Programs.umuloElim a b
          | _ => .Stuck),
        byProgram .bv_smulo_elim (fun
          | .Apply (.Apply (.UOp .bvsmulo) a) b => Programs.smuloElim a b
          | _ => .Stuck)]
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
