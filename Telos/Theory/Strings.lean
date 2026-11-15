import Telos.Theory.Common
import Telos.Rewriter.Rewriter
import Telos.Strings.ArithEntail

/-!
# The strings rewriter (stage 1)

A port of cvc5's `SequencesRewriter` and `StringsRewriter`
(`src/theory/strings/sequences_rewriter.cpp`, `strings_rewriter.cpp`) for
strings. cvc5 rewrites strings only in post-rewriting (`preRewrite` is the
identity), and every change is `REWRITE_AGAIN_FULL`.

Ported so far:

* `rewriteConcat` (`CONCAT_NORM`): nested concatenations flattened, adjacent
  constants merged and empty constants removed. Certified by `aci_norm` (which
  flattens and drops `""`), with each run of constants grouped by `aci_norm`
  and evaluated.
* `rewriteLength`: of a constant (`evaluate`), of a concatenation
  (`str-len-concat-rec`, one child at a time; the arithmetic rewriter then
  normalizes the sum), of `str.rev` (`seq-len-rev`), of `str.update`
  (`str-len-update-inv`), and of `str.replace` and `str.replace_all` when the
  lengths of the pattern and the replacement are equal constants
  (`str-len-replace-inv`).
* `rewriteEquality`: `true` for equal sides, `false` for distinct constants,
  and the orientation by the term order (cvc5: node ids).
* `rewriteCharAt` (`str-at-elim`), `rewritePrefixSuffix` (constants,
  `str-prefixof-one`, `str-prefixof-elim` and their suffix versions; not the
  case decided by arithmetic entailment), and the eliminations of `re.opt`,
  `re.+`, `re.diff` and `re.^`, and `rewriteRangeRegExp`;
* the evaluation of any string operator applied to constants.

Not ported yet: the rest of each function (substrings, containment, replacement,
`indexof`, prefixes, membership in regular expressions, the regular expression
rewrites, conversions), the entailment utilities they rely on
(`ArithEntail`, `StringsEntail`), the length of `str.to_lower` and
`str.to_upper` (CPC has no rule), and sequences.
-/

namespace Telos

namespace StringsRewriter

open Node

def tt : Node := .const (.boolean true)

/-- The membership of a constant string in a regular expression, by
`str-in-re-eval` (Logos's `evaluate` does not reduce `str.in_re`). -/
def inReEval (n : Node) (v : Node) : Option (Rw n) :=
  match n.getKind, n.getChildren with
  | .STRING_IN_REGEXP, #[s, _] => if s.isConst then checkBy .str_in_re_eval n v else none
  | _, _ => none

/-- The proofs of premises that evaluation does not discharge: membership of
constants (`str-in-re-eval`), and arithmetic predicates (`ArithEntail`). -/
def premiseProver (p v : Node) : Option (List Eo.CCmd) :=
  match inReEval p v with
  | some r =>
    match Proof.emitProof r with
    | .ok steps => some (steps.toList.zipIdx.map fun (st, k) => st.toCmd k)
    | .error _ => none
  | none => ArithEntail.premiseProof p v

/-- A rule whose premises are proven by `premiseProver` when evaluation does not
discharge them. -/
def byRuleE (name : String) (n : Node) : Option (Rw n) :=
  rewriteByWith premiseProver name n

def len (t : Node) : Node := mkNode .STRING_LENGTH #[t]

/-- The code points of a string constant. -/
def word? : Node → Option (List Nat)
  | .const (.string cs) => some cs
  | _ => none

def mkWord (cs : List Nat) : Node := .const (.string cs)

/-- cvc5's `utils::mkConcat`: the empty string, the child itself, or the
concatenation. -/
def mkConcat : List Node → Node
  | [] => mkWord []
  | [c] => c
  | cs => mkNode .STRING_CONCAT cs.toArray

/-- The children of cvc5's `rewriteConcat` result: nested concatenations are
spliced in, adjacent constants are merged, and empty constants are dropped. -/
def concatNormChildren (cs : List Node) : List Node :=
  let push (out : List Node) (pre : Option (List Nat)) : List Node :=
    match pre with
    | some w => if w.isEmpty then out else out ++ [mkWord w]
    | none => out
  let flat := cs.flatMap fun c => if c.getKind == .STRING_CONCAT then c.getChildren.toList else [c]
  let (out, pre) := flat.foldl (init := (([] : List Node), (none : Option (List Nat))))
    fun (out, pre) c =>
      match word? c with
      | some w => (out, some ((pre.getD []) ++ w))
      | none => (push out pre ++ [c], none)
  push out pre

/-- `aci_norm`, unless the two nodes are equal. -/
def aci (a b : Node) : Option (Rw a) :=
  if a == b then some (Rw.id a) else checkBy .aci_norm a b

/-- cvc5's `rewriteConcat`, certified: `aci_norm` to flatten and to group each
run of constants into a concatenation of its own, `evaluate` for each group,
and `aci_norm` to drop the empty constants. -/
def rewriteConcat (n : Node) : Option (Rw n) := do
  let cs := n.getChildren.toList
  let target := mkConcat (concatNormChildren cs)
  if target == n then none
  if cs.all (·.isConst) then return ← byEvaluate n
  -- The flattened children, with each run of two or more constants grouped.
  let flat := cs.flatMap fun c => if c.getKind == .STRING_CONCAT then c.getChildren.toList else [c]
  let runs : List (List Node) := flat.foldl (init := []) fun acc c =>
    match acc.getLast?, c.isConst with
    | some last, true =>
      if last.all (·.isConst) then acc.dropLast ++ [last ++ [c]] else acc ++ [[c]]
    | _, _ => acc ++ [[c]]
  let grouped := runs.map fun run => match run with
    | [c] => c
    | run => mkNode .STRING_CONCAT run.toArray
  let g := mkConcat grouped
  let r ← aci n g
  -- Evaluate each group.
  let r ← (List.range grouped.length).foldlM (init := r) fun r i =>
    match grouped[i]? with
    | some (.app (.kind .STRING_CONCAT) _) =>
      if grouped.length == 1 then r.next? byEvaluate
      else r.next? fun m => Rw.congrArg m i byEvaluate
    | _ => some r
  r.next? fun m => aci m target

/-- cvc5's `rewriteLength`. -/
def rewriteLength (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[c] =>
    if c.isConst then byEvaluate n
    else match c.getKind with
      | .STRING_CONCAT => byRule "str-len-concat-rec" n
      | .STRING_REPLACE | .STRING_REPLACE_ALL =>
        -- `LEN_REPL_INV`, when `ArithEntail::checkEq` shows that the pattern and
        -- the replacement have the same length.
        match c.getChildren with
        | #[_, y, z] =>
          if ArithEntail.checkEq (len y) (len z) then
            byRuleE (if c.getKind == .STRING_REPLACE then "str-len-replace-inv"
              else "str-len-replace-all-inv") n
          else none
        | _ => none
      | .STRING_REV => byRule "seq-len-rev" n
      | .STRING_UPDATE => byRule "str-len-update-inv" n
      | _ => none
  | _ => none

/-- cvc5's `rewriteEquality`. -/
def rewriteEquality (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b] =>
    if a == b then byRule "eq-refl" n
    else if a.isConst && b.isConst then byEvaluate n
    else if b.lt a then byRule "eq-symm" n
    else none
  | _ => none

/-- cvc5's `rewritePrefixSuffix`. -/
def rewritePrefixSuffix (n : Node) : Option (Rw n) :=
  let isPrefix := n.getKind == .STRING_PREFIX
  let toEq := fun (_ : Unit) => byRuleE (if isPrefix then "str-prefixof-eq" else "str-suffixof-eq") n
  match n.getChildren with
  | #[a, b] =>
    if a.isConst && b.isConst then byEvaluate n
    else
      match word? b with
      -- `SUF_PREFIX_EMPTY`: (str.prefixof x "") is (= x "")
      | some [] => toEq ()
      | some [_] => byRule (if isPrefix then "str-prefixof-one" else "str-suffixof-one") n
      | _ =>
        -- `SUF_PREFIX_TO_EQS`: the prefix is at least as long as the string
        if ArithEntail.check2 (len a) (len b) then toEq ()
        else byRule (if isPrefix then "str-prefixof-elim" else "str-suffixof-elim") n
  | _ => none

/-- cvc5's `rewriteRangeRegExp`. -/
def rewriteRange (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b] =>
    match word? a, word? b with
    | some wa, some wb =>
      if wa.length != 1 then byRule "re-range-non-singleton-1" n
      else if wb.length != 1 then byRule "re-range-non-singleton-2" n
      else if a == b then byRule "re-range-refl" n
      else if wb.head! < wa.head! then byRule "re-range-emp" n
      else none
    | some wa, none => if wa.length != 1 then byRule "re-range-non-singleton-1" n else none
    | none, some wb => if wb.length != 1 then byRule "re-range-non-singleton-2" n else none
    | none, none => none
  | _ => none

/-- cvc5's `StringsEntail::stripSymbolicLength`, for whole components: strip
components of `cs` from the front (`front`) or the back while `curr` stays
entailed non-negative after subtracting their lengths. Returns the stripped
components, the rest, and what is left of `curr`. cvc5 also strips part of a
constant; telos stops there (cvc5 proves that case by an encoding transform). -/
def stripSymbolicLength (cs : List Node) (front : Bool) (curr : Node) :
    Option (List Node × List Node × Node) :=
  let zero := ArithEntail.zero
  let rec go (rest stripped : List Node) (curr : Node) (fuel : Nat) : List Node × List Node × Node :=
    match fuel, (if front then rest.head? else rest.getLast?) with
    | fuel + 1, some c =>
      if curr == zero then (stripped, rest, curr) else
      let next := ArithEntail.rewriteArith (mkNode .SUB #[curr, len c])
      let ok := match word? c with
        | some w =>
          match ArithEntail.lowerBound? (ArithEntail.rewriteArith curr) with
          | some lb => lb > 0 && lb - w.length ≥ 0
          | none => false
        | none => ArithEntail.check next
      if ok then
        let rest' := if front then rest.tail else rest.dropLast
        let stripped' := if front then stripped ++ [c] else c :: stripped
        go rest' stripped' next fuel
      else (stripped, rest, curr)
    | _, _ => (stripped, rest, curr)
  let (stripped, rest, curr) := go cs [] curr cs.length
  if stripped.isEmpty then none else some (stripped, rest, curr)

/-- cvc5's `rewriteViaMacroSubstrStripSymLength`, certified as cvc5 elaborates
`MACRO_SUBSTR_STRIP_SYM_LENGTH`: the string regrouped by `aci_norm` into the
stripped part and the rest, then `str-substr-len-include-pre` or
`str-substr-full` (`SS_LEN_INCLUDE`), `str-substr-concat2`
(`SS_STRIP_START_PT`) or `str-substr-len-include` (`SS_STRIP_END_PT`), with
their premises by `ArithEntail`. -/
def substrStripSymLength (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[s, i, l] =>
    let zero := ArithEntail.zero
    let cs := ArithEntail.concatChildren s
    -- Regroup `s` as `(str.++ first second)`, then apply `rule`.
    let regroup := fun (first second : List Node) (rule : String) =>
      if first.isEmpty || second.isEmpty then none else
      let g := mkNode .STRING_CONCAT #[mkConcat first, mkConcat second]
      (Rw.id n).next? (fun m => Rw.congrArg m 0 fun c => aci c g) >>= fun r => r.next? (byRuleE rule)
    let lenInclude : Option (Rw n) :=
      if i == zero then
        match stripSymbolicLength cs true l with
        | some (stripped, rest, curr) =>
          if rest.isEmpty then byRuleE "str-substr-full" n
          else if curr == zero then none
          else regroup stripped rest "str-substr-len-include-pre"
        | none => none
      else none
    lenInclude.orElse fun _ =>
    -- `SS_STRIP_START_PT`
    (if i != zero then
      match stripSymbolicLength cs true i with
      | some (stripped, rest, _) => regroup stripped rest "str-substr-concat2"
      | none => none
    else none).orElse fun _ =>
    -- `SS_STRIP_END_PT`
    if l != len s then
      let curr := ArithEntail.rewriteArith (mkNode .SUB #[len s, mkNode .ADD #[i, l]])
      match stripSymbolicLength cs false curr with
      | some (stripped, rest, _) => regroup rest stripped "str-substr-len-include"
      | none => none
    else none
  | _ => none

/-- cvc5's `rewriteSubstr`. -/
def rewriteSubstr (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[s, i, l] =>
    let zero := ArithEntail.zero
    if word? s == some [] then byRule "str-substr-empty-str" n
    -- `SS_CONST_*`: all constant
    else if s.isConst && i.isConst && l.isConst then byEvaluate n
    -- `SS_START_NEG`: the start is negative
    else if ArithEntail.check2 zero i true then byRuleE "str-substr-empty-start-neg" n
    -- `SS_LEN_NON_POS`: the length is not positive
    else if ArithEntail.check2 zero l then byRuleE "str-substr-empty-range" n
    else
    let inner := match s.getKind, s.getChildren with
      | .STRING_SUBSTR, #[_, _, b] =>
        -- `SS_START_GEQ_LEN`
        if ArithEntail.check2 i b then byRuleE "str-substr-substr-start-geq-len" n else none
      | .STRING_REPLACE, #[_, y, z] =>
        -- `SUBSTR_REPL_SWAP`
        if i == zero && ArithEntail.checkLengthOne y true && ArithEntail.checkLengthOne z true then
          byRuleE "str-substr-replace" n
        else none
      | _, _ => none
    inner.orElse fun _ =>
    -- `SS_LEN_ONE_Z_Z`
    (if i == l && ArithEntail.checkLengthOne s then byRuleE "str-substr-char-start-eq-len" n
    else none).orElse fun _ =>
    -- `SS_END_PT_NORM`
    (if ArithEntail.check2 l (len s) true then byRuleE "str-substr-len-norm" n else none).orElse fun _ =>
    (substrStripSymLength n).orElse fun _ =>
    -- combine nested substrings
    match s.getKind, s.getChildren with
    | .STRING_SUBSTR, #[_, n1, m1] =>
      if ArithEntail.check i && ArithEntail.check n1 then
        let fromInner := mkNode .SUB #[m1, i]
        -- `SS_COMBINE_EQ`, `SS_COMBINE_GEQ_INNER`, `SS_COMBINE_GEQ_OUTER`
        if fromInner == l then byRuleE "str-substr-combine1" n
        else if ArithEntail.check2 fromInner l then byRuleE "str-substr-combine2" n
        else if ArithEntail.check2 l fromInner then byRuleE "str-substr-combine1" n
        else none
      else none
    | _, _ => none
  | _ => none

/-! ## Regular expressions -/

def reAllStar : Node := mkNode .REGEXP_STAR #[mkNode .REGEXP_ALLCHAR #[]]
def reNone : Node := mkNode .REGEXP_NONE #[]
def emptyRe : Node := mkNode .STRING_TO_REGEXP #[mkWord []]

/-- A certificate that `cur` rewrites to `target`, by a short search: `aci_norm`
or `absorb` directly, or after one of `ruleNames`. -/
partial def reach (ruleNames : List String) (target : Node) : Nat → (cur : Node) → Option (Rw cur)
  | 0, _ => none
  | fuel + 1, cur =>
    if cur == target then some (Rw.id cur) else
    firstOf [fun _ => aci cur target, fun _ => checkBy .absorb cur target,
      fun _ => (firstOf (ruleNames.map fun r _ => byRuleE r cur)).bind (·.next? (reach ruleNames target fuel))]

/-- cvc5's `rewriteAndOrRegExp`, its flattening part (`RE_ANDOR_FLATTEN`,
`RE_AND_EMPTY`, `RE_OR_ALL`, `RE_INTER_CONST_CONST_CONFLICT`). The macros
`rewriteViaMacroReInterUnionConstElim` and
`rewriteViaMacroReInterUnionInclusion` are not ported. -/
def rewriteAndOr (n : Node) : Option (Rw n) := do
  let nk := n.getKind
  let isInter := nk == .REGEXP_INTER
  -- cvc5's loop: the result, or an early answer.
  let step : (List Node × Bool × Option Node) → Node → (List Node × Bool × Option Node) :=
    fun (vec, changed, early) ni =>
      if early.isSome then (vec, changed, early) else
      if ni.getKind == nk then
        (ni.getChildren.toList.foldl (fun v c => if v.contains c then v else v ++ [c]) vec, true, none)
      else if ni.getKind == .REGEXP_NONE then
        if isInter then (vec, changed, some ni) else (vec, true, none)
      else if ni == reAllStar then
        if !isInter then (vec, changed, some ni) else (vec, true, none)
      else if !vec.contains ni then
        let isConstStr := ni.getKind == .STRING_TO_REGEXP && (ni.getChildren[0]?.map (·.isConst)).getD false
        if isInter && isConstStr &&
            vec.any (fun v => v.getKind == .STRING_TO_REGEXP && (v.getChildren[0]?.map (·.isConst)).getD false) then
          (vec, changed, some reNone)
        else (vec ++ [ni], changed, none)
      else (vec, true, none)
  let (vec, changed, early) := n.getChildren.toList.foldl step ([], false, none)
  let target ← match early with
    | some t => some t
    | none =>
      if !changed then none
      else some (match vec with
        | [] => if isInter then reAllStar else reNone
        | [c] => c
        | cs => mkNode nk cs.toArray)
  if target == n then none
  reach ["re-union-all", "re-inter-all", "re-inter-cstring-neg"] target (n.getChildren.size + 2) n

/-- cvc5's `rewriteStarRegExp`. -/
def rewriteStar (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[r] =>
    match r.getKind with
    | .REGEXP_STAR => byRule "re-star-star" n
    | .REGEXP_NONE => byRule "re-star-none" n
    | .STRING_TO_REGEXP => if r == emptyRe then byRule "re-star-emp" n else none
    | .REGEXP_UNION =>
      if r.getChildren.any (·.getKind == .REGEXP_ALLCHAR) then byRule "re-star-union-char" n
      else if r.getChildren.contains emptyRe then byRule "re-star-union-drop-emp" n
      else none
    | _ => none
  | _ => none

/-- Whether a regular expression has no variables (cvc5's `isConstRegExp`). -/
def isConstRe (r : Node) : Bool := r.vars.isEmpty

/-- cvc5's `rewriteMembership`, without simple consumption
(`rewriteViaStrInReConsume`), inclusion (`rewriteViaMacroStrInReInclusion`),
and the cases of stars over constant strings, of concatenations of
`re.allchar` (`RE_CONCAT_PURE_ALLCHAR`, `RE_IN_CHAR_MODULUS_STAR`) and of
`RE_IN_DIST_CHAR_STAR`. -/
def rewriteMembership (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[x, r] =>
    match r.getKind with
    | .REGEXP_NONE => byRule "re-in-empty" n
    | _ =>
    -- `RE_IN_EVAL`: a constant string in a regular expression without variables
    if x.isConst && isConstRe r then
      (inReEval n (.const (.boolean true))).orElse fun _ => inReEval n (.const (.boolean false))
    else
    match r.getKind with
    | .REGEXP_ALLCHAR => byRule "re-in-sigma" n
    | .REGEXP_STAR =>
      if r.getChildren[0]?.map (·.getKind) == some .REGEXP_ALLCHAR then byRule "re-in-sigma-star" n
      else none
    | .REGEXP_CONCAT =>
      -- `RE_CONCAT_TO_CONTAINS`: (str.in_re x (re.++ _* "abc" _*))
      let rcs := r.getChildren.toList
      let consts := rcs.filter (·.getKind == .STRING_TO_REGEXP)
      if rcs.length ≥ 3 && consts.length == 1 && rcs.all (fun c => c == reAllStar || c.getKind == .STRING_TO_REGEXP)
          && rcs.head? != consts.head? && rcs.getLast? != consts.head? then
        byRule "str-in-re-contains" n
      else none
    | .REGEXP_UNION => byRule "str-in-re-union-elim" n
    | .REGEXP_INTER => byRule "str-in-re-inter-elim" n
    | .STRING_TO_REGEXP => byRule "re-in-cstring" n
    | .REGEXP_RANGE => if isConstRe r then byRule "str-in-re-range-elim" n else none
    | .REGEXP_COMPLEMENT => byRule "re-in-comp" n
    | _ => none
  | _ => none

/-- The value of a string operator applied to constants. -/
def evalConst (n : Node) : Option (Rw n) :=
  let cs := n.getChildren
  if !cs.isEmpty && cs.all (·.isConst) then
    (byEvaluate n).filter (·.1.isConst)
  else none

/-- cvc5's `SequencesRewriter::postRewrite`. -/
def postRewrite (n : Node) : RewriteResponse n :=
  let r : Option (Rw n) := match n.getKind with
    | .STRING_CONCAT => rewriteConcat n
    | .STRING_LENGTH => rewriteLength n
    | .EQUAL => rewriteEquality n
    | .STRING_CHARAT => byRule "str-at-elim" n
    | .STRING_SUBSTR => rewriteSubstr n
    | .STRING_PREFIX | .STRING_SUFFIX => rewritePrefixSuffix n
    | .REGEXP_OPT => byRule "re-opt-elim" n
    | .REGEXP_PLUS => byRule "re-plus-elim" n
    | .REGEXP_DIFF => byRule "re-diff-elim" n
    | .REGEXP_REPEAT => byRule "re-repeat-elim" n
    | .REGEXP_RANGE => rewriteRange n
    | .REGEXP_ALL => byRule "re-all-elim" n
    | .REGEXP_UNION | .REGEXP_INTER => rewriteAndOr n
    | .REGEXP_STAR => rewriteStar n
    | .STRING_IN_REGEXP => rewriteMembership n
    | _ => evalConst n
  match r with
  | some ⟨m, h⟩ =>
    if m == n then .done n
    -- An equality that is only reoriented is done (cvc5's `EQ_SYM` result is
    -- in normal form).
    else if n.getKind == .EQUAL && m.getKind == .EQUAL then ⟨.REWRITE_DONE, m, h⟩
    else ⟨.REWRITE_AGAIN_FULL, m, h⟩
  | none => .done n

end StringsRewriter

/-- cvc5's strings rewriter. Its pre-rewrite is the identity. -/
def TheoryRewriter.strings : TheoryRewriter where
  preRewrite := .done
  postRewrite := StringsRewriter.postRewrite

end Telos
