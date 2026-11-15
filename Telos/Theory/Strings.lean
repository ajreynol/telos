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

/-- A rule whose arithmetic premises are proven by `ArithEntail` when evaluation
does not discharge them. -/
def byRuleE (name : String) (n : Node) : Option (Rw n) :=
  rewriteByWith ArithEntail.premiseProof name n

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

/-- cvc5's `rewriteSubstr`, without `rewriteViaMacroSubstrStripSymLength`. -/
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
