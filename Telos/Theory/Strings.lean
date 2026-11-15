import Telos.Theory.Common
import Telos.Rewriter.Rewriter
import Telos.Strings.ArithEntail
import Telos.Strings.StringsEntail
import Telos.Proof.Emit

/-!
# The strings rewriter (stage 1)

A port of cvc5's `SequencesRewriter` and `StringsRewriter`
(`src/theory/strings/sequences_rewriter.cpp`, `strings_rewriter.cpp`) for
strings. cvc5 rewrites strings only in post-rewriting (`preRewrite` is the
identity), and every change is `REWRITE_AGAIN_FULL`.

Ported so far: `rewriteConcat`, `rewriteLength`, `rewriteEquality`,
`rewriteCharAt`, `rewriteSubstr`, `rewritePrefixSuffix`, `rewriteContains`,
`rewriteReplace`, `rewriteReplaceAll`, `rewriteIndexof`, `rewriteStrReverse`,
the regular expression eliminations, `rewriteRangeRegExp`,
`rewriteAndOrRegExp` (without its macros), `rewriteStarRegExp`, most of
`rewriteMembership`, and from `StringsRewriter` the conversions, `str.<`,
`str.<=` and `str.is_digit`; with the entailments they use (`ArithEntail`,
`StringsEntail`). Each case is certified by CPC rules, as cvc5 elaborates its
macros (see `docs/design.md`, roadmap item 8). Cases that are proof holes in
cvc5 are left unchanged.

The strings rewriter is given the full rewriter (`rw`), which cvc5's
`StringsEntail::checkContains` uses, and which proves premises that evaluation
does not (`premiseProver`).

Not ported yet: `rewriteConcatRegExp`, `rewriteLoopRegExp`, parts of
`rewriteMembership` and `rewriteIndexof`, the length of `str.to_lower` and
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
constants (`str-in-re-eval`), arithmetic predicates (`ArithEntail`), and
otherwise the full rewriter, when it rewrites the premise to its value (as
cvc5's `checkContains` does). -/
def premiseProver (rw : (m : Node) → Rw m) (p v : Node) : Option (List Eo.CCmd) :=
  match inReEval p v with
  | some r => Proof.cmdsOf r
  | none =>
    (ArithEntail.premiseProof p v).orElse fun _ =>
    -- containments that hold by one rule, without the full rewriter
    (if v == .const (.boolean true) then
      (firstOf [fun _ => byRule "str-contains-refl" p, fun _ => byRule "str-substr-ctn" p]).bind
        fun r => if r.1 == v then Proof.cmdsOf r else none
    else none).orElse fun _ =>
      let r := rw p
      if r.1 == v then Proof.cmdsOf r else none

/-- A rule whose premises are proven by `premiseProver` when evaluation does not
discharge them. -/
def byRuleE (rw : (m : Node) → Rw m) (name : String) (n : Node) : Option (Rw n) :=
  rewriteByWith (premiseProver rw) name n

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
def rewriteLength (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
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
            byRuleE rw (if c.getKind == .STRING_REPLACE then "str-len-replace-inv"
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
def rewritePrefixSuffix (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  let isPrefix := n.getKind == .STRING_PREFIX
  let toEq := fun (_ : Unit) => byRuleE rw (if isPrefix then "str-prefixof-eq" else "str-suffixof-eq") n
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
def substrStripSymLength (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[s, i, l] =>
    let zero := ArithEntail.zero
    let cs := ArithEntail.concatChildren s
    -- Regroup `s` as `(str.++ first second)`, then apply `rule`.
    let regroup := fun (first second : List Node) (rule : String) =>
      if first.isEmpty || second.isEmpty then none else
      let g := mkNode .STRING_CONCAT #[mkConcat first, mkConcat second]
      (Rw.id n).next? (fun m => Rw.congrArg m 0 fun c => aci c g) >>= fun r => r.next? (byRuleE rw rule)
    let lenInclude : Option (Rw n) :=
      if i == zero then
        match stripSymbolicLength cs true l with
        | some (stripped, rest, curr) =>
          if rest.isEmpty then byRuleE rw "str-substr-full" n
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
def rewriteSubstr (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[s, i, l] =>
    let zero := ArithEntail.zero
    if word? s == some [] then byRule "str-substr-empty-str" n
    -- `SS_CONST_*`: all constant
    else if s.isConst && i.isConst && l.isConst then byEvaluate n
    -- `SS_START_NEG`: the start is negative
    else if ArithEntail.check2 zero i true then byRuleE rw "str-substr-empty-start-neg" n
    -- `SS_LEN_NON_POS`: the length is not positive
    else if ArithEntail.check2 zero l then byRuleE rw "str-substr-empty-range" n
    else
    let inner := match s.getKind, s.getChildren with
      | .STRING_SUBSTR, #[_, _, b] =>
        -- `SS_START_GEQ_LEN`
        if ArithEntail.check2 i b then byRuleE rw "str-substr-substr-start-geq-len" n else none
      | .STRING_REPLACE, #[_, y, z] =>
        -- `SUBSTR_REPL_SWAP`
        if i == zero && ArithEntail.checkLengthOne y true && ArithEntail.checkLengthOne z true then
          byRuleE rw "str-substr-replace" n
        else none
      | _, _ => none
    inner.orElse fun _ =>
    -- `SS_LEN_ONE_Z_Z`
    (if i == l && ArithEntail.checkLengthOne s then byRuleE rw "str-substr-char-start-eq-len" n
    else none).orElse fun _ =>
    -- `SS_END_PT_NORM`
    (if ArithEntail.check2 l (len s) true then byRuleE rw "str-substr-len-norm" n else none).orElse fun _ =>
    (substrStripSymLength rw n).orElse fun _ =>
    -- combine nested substrings
    match s.getKind, s.getChildren with
    | .STRING_SUBSTR, #[_, n1, m1] =>
      if ArithEntail.check i && ArithEntail.check n1 then
        let fromInner := mkNode .SUB #[m1, i]
        -- `SS_COMBINE_EQ`, `SS_COMBINE_GEQ_INNER`, `SS_COMBINE_GEQ_OUTER`
        if fromInner == l then byRuleE rw "str-substr-combine1" n
        else if ArithEntail.check2 fromInner l then byRuleE rw "str-substr-combine2" n
        else if ArithEntail.check2 l fromInner then byRuleE rw "str-substr-combine1" n
        else none
      else none
    | _, _ => none
  | _ => none

/-! ## Containment -/

open StringsEntail (getConcat Components componentContains stripConstantEndpoints checkMultisetSubset)

def ctnNode (a b : Node) : Node := mkNode .STRING_CONTAINS #[a, b]

/-- cvc5's `StringsEntail::checkContains`: the value of `(str.contains a b)`
after rewriting it with the full rewriter, when it is a constant. -/
def checkContains (rw : (m : Node) → Rw m) (a b : Node) : Option Bool :=
  match (rw (ctnNode a b)).1 with
  | .const (.boolean v) => some v
  | _ => none

/-- `s` regrouped as the concatenation `g` of the same components, where `g`
may split a constant of `s` or add empty constants: by `aci_norm`, or by
rewriting `g` back to `s` (cvc5's `rewriteConcat`), reversed. -/
def regroup (s g : Node) : Option (Rw s) :=
  if s == g then some (Rw.id s) else
  (aci s g).orElse fun _ =>
    if g.getKind == .STRING_CONCAT then rewriteConcat g >>= Proof.reverse s else none

/-- A concatenation with nested concatenations flattened at every depth, by
`rewriteConcat` from the inside out. -/
partial def rewriteConcatDeep (m : Node) : Option (Rw m) :=
  let cs := m.getChildren
  let r := (List.range cs.size).foldl (init := Rw.id m) fun r i =>
    r.next fun k => Rw.congrArg k i fun c =>
      if c.getKind == .STRING_CONCAT then rewriteConcatDeep c else none
  if r.1.getKind == .STRING_CONCAT then some (r.next rewriteConcat) else some r

/-- `MACRO_STR_COMPONENT_CTN`, certified as cvc5 elaborates it: the first
argument regrouped around the components of the second (`componentContains`
with remainders), then `str-contains-concat-find` with the premise
`(str.contains b b)`. -/
def componentCtn (rw : (m : Node) → Rw m) (n a b : Node) : Option (Rw n) := do
  let cc ← componentContains (checkContains rw) false (getConcat a) (getConcat b) true
  let parts := [cc.before, cc.mid, cc.after].filter (!·.isEmpty) |>.map mkConcat
  let r ← Rw.congrArg n 0 fun c => regroup c (mkConcat parts)
  if parts.length == 1 then r.next? (byRule "str-contains-refl")
  else r.next? (byRuleE rw "str-contains-concat-find")

/-- `MACRO_STR_STRIP_ENDPOINTS` for `str.contains` and `str.replace`, certified
as cvc5 elaborates it: both arguments regrouped as three components, the
stripped ones first and last (or `""`), then `str-overlap-endpoints-ctn` (or
`-replace`), then `aci_norm` back. -/
def stripEndpoints (n : Node) : Option (Rw n) := do
  let cs := n.getChildren
  let a ← cs[0]?
  let b ← cs[1]?
  let isCtn := n.getKind == .STRING_CONTAINS
  let isIdof := n.getKind == .STRING_INDEXOF
  if isIdof && cs[2]? != some ArithEntail.zero then none
  let nc2 := getConcat b
  let dirs : List Int := if isIdof then [-1] else if b.isConst then [-1, 1] else [0]
  let (nb, rem, ne) ← dirs.findSome? (stripConstantEndpoints (getConcat a) nc2)
  if nb.length > 1 || ne.length > 1 then none
  let emp := mkWord []
  let (d1, nc2) := if nb.isEmpty then (emp, nc2) else (nc2.head!, nc2.drop 1)
  let (d2, nc2) := if ne.isEmpty then (emp, nc2) else (nc2.getLast!, nc2.dropLast)
  let c1 := nb.headD emp
  let c2 := ne.headD emp
  let remN := mkConcat rem
  if isIdof then
    -- only the end is stripped
    let g1 := mkNode .STRING_CONCAT #[remN, c2]
    let g2 := mkNode .STRING_CONCAT #[mkConcat nc2, d2]
    let r ← Rw.congrArg n 0 fun c => regroup c g1
    let r ← r.next? fun m => Rw.congrArg m 1 fun c => aci c g2
    let r ← r.next? fun m => checkBy .str_overlap_endpoints_indexof m (mkNode .STRING_INDEXOF #[remN, g2, ArithEntail.zero])
    return ← r.next? fun m => Rw.congrArg m 1 fun c => aci c b
  let g1 := mkNode .STRING_CONCAT #[c1, remN, c2]
  let g2 := mkNode .STRING_CONCAT #[d1, mkConcat nc2, d2]
  let r ← Rw.congrArg n 0 fun c => regroup c g1
  let r ← r.next? fun m => Rw.congrArg m 1 fun c => aci c g2
  if isCtn then
    let r ← r.next? fun m => checkBy .str_overlap_endpoints_ctn m (ctnNode remN g2)
    r.next? fun m => Rw.congrArg m 1 fun c => aci c b
  else
    let z ← cs[2]?
    let inner := mkNode .STRING_REPLACE #[remN, g2, z]
    let r ← r.next? fun m => checkBy .str_overlap_endpoints_replace m (mkNode .STRING_CONCAT #[c1, inner, c2])
    let r ← r.next? fun m => Rw.congrArg m 1 fun c => Rw.congrArg c 1 fun d => aci d b
    r.next? fun m => aci m (mkConcat (nb ++ [mkNode .STRING_REPLACE #[remN, b, z]] ++ ne))

/-- `MACRO_STR_SPLIT_CTN`: `(str.contains (str.++ s c t) d)` is
`(or (str.contains s d) (str.contains t d))` when the constant `c` and `d`
do not overlap (`str-overlap-split-ctn`, after regrouping by `aci_norm`). -/
def splitCtn (n a b : Node) : Option (Rw n) := do
  let wb ← word? b
  if wb.isEmpty || a.getKind != .STRING_CONCAT then none
  let cs := a.getChildren.toList
  let i ← (List.range cs.length).find? fun i =>
    0 < i && i + 1 < cs.length &&
    match word? cs[i]! with
    | some wc => !Word.hasOverlap wc wb false && !Word.hasOverlap wb wc false
    | none => false
  let pre := mkConcat (cs.take i)
  let post := mkConcat (cs.drop (i + 1))
  let r ← Rw.congrArg n 0 fun c => aci c (mkNode .STRING_CONCAT #[pre, cs[i]!, post])
  r.next? fun m => checkBy .str_overlap_split_ctn m
    (mkNode .OR #[ctnNode pre b, ctnNode post b])

/-- `(str.contains (str.++ x y z) w)` for a character `w`, split into a
disjunction over the components by `str-contains-split-char`, one at a time. -/
partial def splitChar (rw : (m : Node) → Rw m) (m : Node) : Option (Rw m) :=
  match m.getChildren with
  | #[a, _] =>
    if a.getKind == .STRING_CONCAT && a.getChildren.size ≥ 2 then
      (byRuleE rw "str-contains-split-char" m).bind fun r =>
        r.next? fun k => Rw.congrArg k 1 (splitChar rw)
    else some (Rw.id m)
  | _ => none

/-- cvc5's `rewriteContains`. Each case is `some r` when cvc5 rewrites, with
`r` the certificate (`none` when telos cannot certify it, and leaves the node
as it is). -/
def rewriteContains (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b] =>
    let ctn := checkContains rw
    let ff := Node.const (.boolean false)
    let lenA := len a
    let lenB := len b
    let nc1 := getConcat a
    let nc2 := getConcat b
    -- `CTN_CONCAT_CHAR`: remembered, and used if no other case applies
    let maybeRew : Option (Unit → Option (Rw n)) :=
      if (word? b).map List.length == some 1 && a.getKind == .STRING_CONCAT then
        some fun _ => do
          let target := mkNode .OR (nc1.map (ctnNode · b)).toArray
          let r ← splitChar rw n
          r.next? fun m => aci m target
      else none
    let cases : List (Unit → Option (Option (Rw n))) := [
      -- `CTN_EQ`
      fun _ => if a == b then some (byRule "str-contains-refl" n) else none,
      fun _ => if !a.isConst then none else
        -- `CTN_CONST`
        if b.isConst then some (byEvaluate n)
        else if word? a == some [] then
          -- `CTN_LHS_EMPTYSTR`, certified as cvc5 does, by the multiset rule
          if ArithEntail.check lenB true then some (checkBy .str_ctn_multiset_subset n ff) else none
        -- `CTN_SPLIT` for a constant first argument: no CPC rule (a proof
        -- hole in cvc5)
        else if ArithEntail.checkLengthOne b then some none
        else none,
      fun _ => match word? b with
        -- `CTN_RHS_EMPTYSTR`
        | some [] => some (byRuleE rw "str-contains-emp" n)
        | some [_] =>
          match a.getKind, a.getChildren with
          | .STRING_REPLACE, #[_, y, _] =>
            -- `CTN_REPL_CHAR`
            if ctn y b == some false then some (byRuleE rw "str-contains-repl-char" n) else none
          | _, _ => none
        | _ => none,
      -- `CTN_COMPONENT`
      fun _ => if (componentContains ctn false nc1 nc2).isSome then some (componentCtn rw n a b) else none,
      -- `CTN_CONCAT_CTN_SUBSTR`
      fun _ => match b.getKind, b.getChildren with
        | .STRING_SUBSTR, #[s, _, _] =>
          if nc1.contains s then
            some (if a == s then byRule "str-substr-ctn" n else byRuleE rw "str-contains-concat-find" n)
          else none
        | _, _ => none,
      -- `CTN_STRIP_ENDPT`
      fun _ => (stripEndpoints n).map some,
      fun _ => nc2.findSome? fun c =>
        -- `CTN_CONCAT_COM_NON_CTN`
        if nc2.length > 1 && ctn a c == some false then
          some (byRuleE rw "str-contains-concat-find-contra" n)
        else match c.getKind, c.getChildren with
          -- `CTN_RPL_NON_CTN`
          | .STRING_REPLACE, #[t, _, u] =>
            if ctn a t == some false && ctn a u == some false then
              some (if c == b then byRuleE rw "str-replace-dual-ctn-false" n
                else byRuleE rw "str-contains-concat-find-contra" n)
            else none
          | _, _ => none,
      -- `CTN_LEN_INEQ`: certified when the multiset rule applies (cvc5 goes
      -- through `str-eq-len-false`, whose premise telos cannot prove yet)
      fun _ => if ArithEntail.check2 lenB lenA true then some (checkBy .str_ctn_multiset_subset n ff) else none,
      -- `CTN_MSET_NSS`
      fun _ => if checkMultisetSubset a b then some (checkBy .str_ctn_multiset_subset n ff) else none,
      -- `CTN_LEN_INEQ_NSTRICT`
      fun _ => if ArithEntail.check2 lenB lenA then some (byRuleE rw "str-contains-leq-len-eq" n) else none,
      fun _ => match a.getKind, a.getChildren with
        -- `CTN_SPLIT`
        | .STRING_CONCAT, _ => (splitCtn n a b).map some
        -- `CTN_SUBSTR`
        | .STRING_SUBSTR, #[_, _, l] =>
          if l == lenB then some (byRuleE rw "str-contains-leq-len-eq" n) else none
        | .STRING_REPLACE, #[x, y, z] =>
          if x == z && y == b then some (byRule "str-contains-repl-self" n)
          else if x == z && ArithEntail.checkLengthOne b then
            some (byRuleE rw "str-contains-repl-self-tgt-char" n)
          else if z == b then some (byRule "str-contains-repl-tgt" n)
          else none
        -- `CTN_ITOS_NON_DIGIT`
        | .STRING_ITOS, _ =>
          match word? b with
          | some wb => if !Word.isNumber wb then some (byRuleE rw "str-from-int-no-ctn-nondigit" n) else none
          | none => none
        | _, _ => none,
      fun _ => match b.getKind, b.getChildren with
        | .STRING_REPLACE, #[t, s, u] =>
          -- `CTN_REPL`
          if a == s && t == u then some (byRule "str-replace-self-ctn-simp" n)
          -- `CTN_REPL_EMPTY`
          else if a == s && word? t == some [] then some (byRuleE rw "str-replace-emp-ctn-src" n)
          else none
        | _, _ => none,
      fun _ => maybeRew.map fun f => f ()]
    (cases.findSome? fun c => c ()).join
  | _ => none

/-! ## Replacement -/

def replNode (a b c : Node) : Node := mkNode .STRING_REPLACE #[a, b, c]

/-- cvc5's `StringsEntail::checkNonEmpty`. -/
def checkNonEmpty (a : Node) : Bool :=
  match word? a with
  | some w => !w.isEmpty
  | none => ArithEntail.check (ArithEntail.rewriteArith (len a)) true

/-- `rewriteReplaceInternal`, the rewrites shared by `str.replace` and
`str.replace_all`. -/
def rewriteReplaceInternal (rw : (m : Node) → Rw m) (n : Node) : Option (Option (Rw n)) :=
  let isAll := n.getKind == .STRING_REPLACE_ALL
  match n.getChildren with
  | #[a, b, c] =>
    -- `RPL_ID`
    if b == c then some (byRule (if isAll then "str-replace-all-id" else "str-replace-id") n)
    -- `RPL_REPLACE`
    else if a == b && (!isAll || checkNonEmpty b) then
      some (if isAll then byRuleE rw "str-replace-all-self" n else byRule "str-replace-self" n)
    else none
  | _ => none

/-- `(str.replace (str.++ ts t ss t) s r)` is
`(str.++ (str.replace (str.++ ts t ss) s r) t)` for a character `s`
(`str-replace-one-pre`), `k` times, each on the inner replacement. -/
def replaceOnePre (rw : (m : Node) → Rw m) : Nat → (m : Node) → Option (Rw m)
  | 0, m => some (Rw.id m)
  | k + 1, m => do
    let r ← byRuleE rw "str-replace-one-pre" m
    r.next? fun m' => Rw.congrArg m' 0 (replaceOnePre rw k)

/-- The children of `n` (an application) other than the first. -/
def tailChildren (n : Node) : List Node := n.getChildren.toList.drop 1

/-- cvc5's `rewriteReplace`. Each case is `some r` when cvc5 rewrites, with `r`
the certificate (`none` when telos cannot certify it). -/
def rewriteReplace (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b, z] =>
    let ctn := checkContains rw
    let children0 := getConcat a
    let children1 := getConcat b
    let cases : List (Unit → Option (Option (Rw n))) := [
      fun _ => match word? b, word? children0.head! with
        | some t, some s =>
          match Word.find s t with
          | none =>
            -- `RPL_CONST_NFIND`
            if children0.length == 1 then
              some (if z.isConst then byEvaluate n else byRuleE rw "str-replace-no-contains" n)
            else none
          | some p =>
            -- `RPL_CONST_FIND`
            if children0.length == 1 && z.isConst then some (byEvaluate n) else
            let s1 := s.take p
            let s3 := s.drop (p + t.length)
            let target := mkConcat ((if s1.isEmpty then [] else [mkWord s1]) ++ [z] ++
              (if s3.isEmpty then [] else [mkWord s3]) ++ children0.drop 1)
            let rule := if children0.length == 1 then "str-replace-find-base" else "str-replace-find-first-concat"
            some ((byRuleE rw rule n).bind fun r => r.next? fun m => aci m target)
        | _, _ => none,
      -- `RPL_RPL_EMPTY`
      fun _ => if word? b == some [] then some (byRuleE rw "str-replace-empty" n) else none,
      fun _ => rewriteReplaceInternal rw n,
      -- `RPL_RPL_LEN_ID`
      fun _ => if a == z && ArithEntail.check2 (len b) (len a) then some (byRuleE rw "str-repl-repl-len-id" n) else none,
      fun _ => match ctn a b with
        | some true =>
          match componentContains ctn false children0 children1 true 1 with
          | some cc =>
            if cc.index == 0 && children0.head? == children1.head? then
              -- `RPL_CCTN_RPL`: a prefix
              let target := mkConcat (z :: cc.after)
              some do
                let r ← Rw.congrArg n 0 fun c => regroup c (mkConcat (children1 ++ cc.after))
                let r ← r.next? fun m => firstOf [fun _ => byRule "str-replace-prefix-concat" m,
                  fun _ => byRule "str-replace-prefix" m]
                if r.1 == target then some r else r.next? fun m => aci m target
            else if !cc.after.isEmpty then
              -- `RPL_CCTN`: what is after the first match is pulled out
              let target := mkConcat (replNode (mkConcat cc.mid) b z :: cc.after)
              some do
                let cc0 ← componentContains ctn false children0 children1 true 0
                let g := mkConcat (cc0.before ++ [b] ++ cc0.after)
                let r ← Rw.congrArg n 0 fun c => regroup c g
                let r ← r.next? (byRule "str-replace-find-pre")
                if r.1 == target then some r else
                let r ← r.next? fun m => Rw.congrArg m 0 fun c => Rw.congrArg c 0 fun d =>
                  if d.getKind == .STRING_CONCAT then rewriteConcat d else none
                if r.1 == target then some r else r.next? fun m => aci m target
            else none
          | none => none
        -- `RPL_NCTN`
        | some false => some (byRuleE rw "str-replace-no-contains" n)
        | none => none,
      -- `RPL_PULL_ENDPT`
      fun _ => if checkNonEmpty b then (stripEndpoints n).map some else none,
      -- `REPL_SUBST_IDX`: no CPC rule (a proof hole in cvc5)
      fun _ =>
        match children1.getLast? with
        | some (.app (.kind .STRING_SUBSTR) #[_, _, j]) =>
          let partLen := len (mkConcat children1.dropLast)
          if ArithEntail.check2 (mkNode .ADD #[partLen, j])
              (mkNode .ADD #[len a, ArithEntail.one]) true then some none else none
        | _ => none,
      fun _ => match a.getKind, a.getChildren with
        | .STRING_REPLACE, #[y', w, y''] =>
          -- `REPL_REPL_SHORT_CIRCUIT`
          if y' == y'' && y' == b && ArithEntail.check2 (len w) (len z) && w != z && w.isConst && z.isConst then
            some (byRuleE rw "str-repl-repl-lookahead-id-simp" n)
          else none
        | _, _ => none,
      fun _ => match b.getKind, b.getChildren with
        | .STRING_REPLACE, #[b0, b1, b2] =>
          let dual : Option (Option (Rw n)) :=
            if b0 == a then
              -- `REPL_REPL2_INV_ID`
              if b0 == b2 && b0 == z then some (byRule "str-repl-repl-dual-self" n)
              -- `REPL_DUAL_REPL_ITE`
              else if ctn b0 b2 == some false then some (byRuleE rw "str-repl-repl-dual-ite1" n)
              else if ctn b1 b2 == some false && ctn b2 b1 == some false then
                some (byRuleE rw "str-repl-repl-dual-ite2" n)
              else none
            else none
          dual.orElse fun _ =>
          -- `REPL_REPL2_INV`
          if b1 == a then
            if b0 == b2 then some (byRule "str-repl-repl-src-self" n)
            else if (b1 == z || b0 == z) && ctn b0 b2 == some false then
              some (firstOf [fun _ => byRuleE rw "str-repl-repl-src-inv-no-ctn1" n,
                fun _ => byRuleE rw "str-repl-repl-src-inv-no-ctn2" n])
            else none
          else if ctn a b1 == some false && ctn a b2 == some false then
            some (byRuleE rw "str-repl-repl-src-inv-no-ctn3" n)
          else none
        | _, _ => none,
      fun _ => match z.getKind, z.getChildren with
        | .STRING_REPLACE, #[z0, z1, z2] =>
          -- `REPL_REPL3_INV`
          (if z1 == a && ctn z0 b == some false then some (byRuleE rw "str-repl-repl-src-tgt-no-ctn" n)
          else none).orElse fun _ =>
          -- `REPL_REPL3_INV_ID`
          if z0 == b then
            if z0 == z2 && z1 == a then some (byRule "str-repl-repl-tgt-self" n)
            else if ctn a z1 == some false then some (byRuleE rw "str-repl-repl-tgt-no-ctn" n)
            else none
          else none
        | _, _ => none,
      -- `REPL_CHAR_NCONTRIB_FIND`
      fun _ =>
        if !ArithEntail.checkLengthOne b then none else
        let k := children0.length
        -- the number of trailing components contained in what precedes them
        let rec count (i : Nat) (fuel : Nat) : Nat :=
          match fuel with
          | 0 => i - 1
          | fuel + 1 =>
            if i < k && ctn (mkConcat (children0.take (k - i))) children0[k - i]! == some true then
              count (i + 1) fuel
            else i - 1
        let m := count 1 k
        if m == 0 then none else
        let lastLhs := mkConcat (children0.take (k - m))
        let target := mkConcat (replNode lastLhs b z :: children0.drop (k - m))
        some do
          let r ← replaceOnePre rw m n
          if r.1 == target then some r else r.next? fun m => aci m target]
    (cases.findSome? fun c => c ()).join
  | _ => none

/-- `(str.replace_all s t r)` for constants `s` and `t` and a symbolic `r`:
`str-replace-all-find` at each occurrence, then `str-replace-all-no-contains`. -/
partial def replaceAllConst (rw : (m : Node) → Rw m) (m : Node) : Option (Rw m) :=
  (byRuleE rw "str-replace-all-find" m).bind (fun r =>
    r.next? fun k => Rw.congrArg k 2 (replaceAllConst rw)) |>.orElse fun _ =>
  byRuleE rw "str-replace-all-no-contains" m

/-- cvc5's `rewriteReplaceAll`. -/
def rewriteReplaceAll (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b, z] =>
    let cases : List (Unit → Option (Option (Rw n))) := [
      fun _ => match word? a, word? b with
        | some s, some t =>
          -- `REPLALL_EMPTY_FIND`, `REPLALL_CONST`
          if z.isConst then some (byEvaluate n)
          else if t.isEmpty then some (byRuleE rw "str-replace-all-empty" n)
          else if s.isEmpty then some (byRuleE rw "str-replace-all-no-contains" n)
          else
            -- the pieces of `s` between the occurrences of `t`
            let rec pieces (s : List Nat) (fuel : Nat) : List Node :=
              match fuel, Word.find s t with
              | fuel + 1, some p => (if p > 0 then [mkWord (s.take p)] else []) ++ [z] ++ pieces (s.drop (p + t.length)) fuel
              | _, _ => if s.isEmpty then [] else [mkWord s]
            let target := mkConcat (pieces s (s.length + 1))
            some do
              let r ← replaceAllConst rw n
              if r.1 == target then some r else
              let r ← r.next? fun m => if m.getKind == .STRING_CONCAT then rewriteConcatDeep m else none
              if r.1 == target then some r else r.next? fun m => aci m target
        | _, _ => none,
      fun _ => rewriteReplaceInternal rw n,
      -- `RPL_NCTN`
      fun _ => if checkContains rw a b == some false then some (byRuleE rw "str-replace-all-no-contains" n) else none]
    (cases.findSome? fun c => c ()).join
  | _ => none

/-! ## `str.indexof` -/

def negOne : Node := .const (.integer (-1))

/-- cvc5's `rewriteIndexof`. Each case is `some r` when cvc5 rewrites, with `r`
the certificate (`none` when telos cannot certify it). -/
def rewriteIndexof (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b, z] =>
    let ctn := checkContains rw
    let zero := ArithEntail.zero
    let children0 := getConcat a
    let children1 := getConcat b
    let zNeg : Bool := match z with | .const (.integer i) => decide (i < 0) | _ => false
    let len0 := len a
    let cases : List (Unit → Option (Option (Rw n))) := [
      -- `IDOF_NEG`
      fun _ => if zNeg then some (byRuleE rw "str-indexof-oob2" n) else none,
      -- `IDOF_FIND`, `IDOF_NFIND`
      fun _ => match word? children0.head!, word? b, z with
        | some s, some t, .const (.integer i) =>
          match Word.find s t i.toNat with
          | some _ =>
            if children0.length == 1 then some (byEvaluate n)
            else some (firstOf [fun _ => (byRuleE rw "str-indexof-contains-pre" n).bind (·.next? byEvaluate),
              fun _ => byRuleE rw "str-indexof-find-emp" n])
          | none => if children0.length == 1 then some (byEvaluate n) else none
        | _, _, _ => none,
      fun _ => if a != b then none else
        -- `IDOF_EQ_CST_START`, `IDOF_EQ_NSTART`, `IDOF_EQ_NORM`
        let self := byRule "str-indexof-self" n
        if z == zero then some (self.bind (·.next? byEvaluate))
        else if ArithEntail.check z true then
          some (self.bind fun r => r.next? fun m => firstOf [fun _ => byEvaluate m, fun _ => byRuleE rw "str-indexof-oob" m])
        else if word? a != some [] then some self
        else none,
      -- `IDOF_EMP_IDOF`
      fun _ => if word? b == some [] && ArithEntail.check2 len0 z && ArithEntail.check z then
          some (byRuleE rw "str-indexof-find-emp" n) else none,
      -- `IDOF_LEN`
      fun _ => if ArithEntail.check2 (len b) (mkNode .SUB #[len0, z]) true then
          some (firstOf [fun _ => byRuleE rw "str-indexof-len-oob" n, fun _ => byRuleE rw "str-indexof-len-oob2" n,
            fun _ => byRuleE rw "str-indexof-oob" n])
        else none,
      fun _ =>
        let fstr := if z == zero then a else mkNode .STRING_SUBSTR #[a, z, len0]
        match ctn fstr b with
        -- `IDOF_NCTN`
        | some false => some (byRuleE rw "str-indexof-no-contains" n)
        | some true =>
          if z == zero then
            match componentContains ctn false children0 children1 true 1 with
            | some cc =>
              if !cc.after.isEmpty then
                -- `IDOF_DEF_CTN`: what is after the first match is dropped
                let target := mkNode .STRING_INDEXOF #[mkConcat cc.mid, b, z]
                some do
                  let cc0 ← componentContains ctn false children0 children1 true 0
                  let g := mkConcat (cc0.before ++ [b] ++ cc0.after)
                  let r ← Rw.congrArg n 0 fun c => regroup c g
                  let r ← r.next? (byRule "str-indexof-contains-concat-pre")
                  if r.1 == target then some r else
                  let r ← r.next? fun m => Rw.congrArg m 0 fun c => if c.getKind == .STRING_CONCAT then rewriteConcat c else none
                  if r.1 == target then some r else none
              -- `IDOF_STRIP_CNST_ENDPTS`: no CPC rule (a proof hole in cvc5)
              else if (stripConstantEndpoints children0 children1 1).isSome then some none
              else none
            | none =>
              if (stripConstantEndpoints children0 children1 1).isSome then some none else none
          else none
        | none => none,
      -- `RPL_PULL_ENDPT`
      fun _ => if z == zero then (stripEndpoints n).map some else none]
    (cases.findSome? fun c => c ()).join
  | _ => none

/-! ## Other string operators -/

/-- `f` applied to each component of a concatenation, one at a time from the
front by `rule` (`(f (str.++ x y z))` is `(str.++ (f x) (f (str.++ y z)))`),
then flattened. -/
partial def minscopeConcat (rule : String) (m : Node) : Option (Rw m) :=
  match m.getChildren with
  | #[c] =>
    if c.getKind == .STRING_CONCAT && c.getChildren.size ≥ 2 then
      (byRule rule m).bind fun r => r.next? fun k => Rw.congrArg k 1 (minscopeConcat rule)
    else some (Rw.id m)
  | _ => none

/-- cvc5's `rewriteStrReverse`. -/
def rewriteStrReverse (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[x] =>
    if x.isConst then byEvaluate n else
    match x.getKind, x.getChildren with
    | .STRING_CONCAT, cs =>
      -- `seq-rev-concat` peels off the last component
      let target := mkNode .STRING_CONCAT (cs.reverse.map fun c => mkNode .STRING_REV #[c])
      let rec go (m : Node) (fuel : Nat) : Option (Rw m) :=
        match fuel, m.getChildren with
        | fuel + 1, #[c] =>
          if c.getKind == .STRING_CONCAT then
            (byRule "seq-rev-concat" m).bind fun r => r.next? fun k => Rw.congrArg k 1 (go · fuel)
          else some (Rw.id m)
        | _, _ => some (Rw.id m)
      (go n cs.size).bind fun r =>
        if r.1 == target then some r else r.next? fun m =>
          if m.getKind == .STRING_CONCAT then (rewriteConcatDeep m).bind fun r' =>
            if r'.1 == target then some r' else none else none
    | .STRING_REV, _ => byRule "seq-rev-rev" n
    | _, _ => none
  | _ => none

/-- cvc5's `rewriteStrConvert` (`str.to_lower`, `str.to_upper`). -/
def rewriteStrConvert (n : Node) : Option (Rw n) :=
  let lower := n.getKind == .STRING_TO_LOWER
  match n.getChildren with
  | #[x] =>
    if x.isConst then byEvaluate n else
    match x.getKind, x.getChildren with
    | .STRING_CONCAT, cs =>
      let target := mkNode .STRING_CONCAT (cs.map fun c => mkNode n.getKind #[c])
      (minscopeConcat (if lower then "str-to-lower-concat" else "str-to-upper-concat") n).bind fun r =>
        if r.1 == target then some r else r.next? fun m =>
          if m.getKind == .STRING_CONCAT then (rewriteConcatDeep m).bind fun r' =>
            if r'.1 == target then some r' else none else none
    | .STRING_TO_LOWER, _ => byRule (if lower then "str-to-lower-idem" else "str-to-upper-lower") n
    | .STRING_TO_UPPER, _ => byRule (if lower then "str-to-lower-upper" else "str-to-upper-idem") n
    | .STRING_ITOS, _ => byRule (if lower then "str-to-lower-from-int" else "str-to-upper-from-int") n
    | _, _ => none
  | _ => none

/-- cvc5's `rewriteStrToInt`. -/
def rewriteStrToInt (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[x] =>
    if x.isConst then byEvaluate n
    else if x.getKind == .STRING_CONCAT &&
        x.getChildren.any (fun c => match word? c with | some w => !Word.isNumber w | none => false) then
      -- `STOI_CONCAT_NONNUM`
      byRuleE rw "str-to-int-concat-neg-one" n
    else none
  | _ => none

/-- cvc5's `rewriteStringLeq`. -/
def rewriteStringLeq (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b] =>
    -- `STR_LEQ_ID`: no CPC rule (a proof hole in cvc5)
    if a == b then none
    else if a.isConst && b.isConst then byEvaluate n
    -- `STR_LEQ_EMPTY`
    else if word? a == some [] then byRule "str-leq-empty" n
    else if word? b == some [] then byRule "str-leq-empty-eq" n
    else
    -- `STR_LEQ_CPREFIX`: the constant prefixes differ
    let n1 := getConcat a
    let n2 := getConcat b
    match word? n1.head!, word? n2.head! with
    | some s, some t =>
      if n1.head! == n2.head! then none else
      let l := min s.length t.length
      if s.take l == t.take l then none else
      -- each side as its prefix of length `l`, then the rest
      let split (cs : List Node) (w : List Nat) : Node :=
        let rest := (if w.length > l then [mkWord (w.drop l)] else []) ++ cs.drop 1
        if rest.isEmpty then mkWord (w.take l) else mkNode .STRING_CONCAT (mkWord (w.take l) :: rest).toArray
      let ga := split n1 s
      let gb := split n2 t
      do
        let r ← Rw.congrArg n 0 fun c => regroup c ga
        let r ← r.next? fun m => Rw.congrArg m 1 fun c => regroup c gb
        r.next? fun m =>
          match ga.getKind == .STRING_CONCAT, gb.getKind == .STRING_CONCAT with
          | true, true => firstOf [fun _ => byRule "str-leq-concat-false" m, fun _ => byRule "str-leq-concat-true" m]
          | true, false => (byRule "str-leq-concat-base-1" m).bind (·.next? byEvaluate)
          | false, true => (byRule "str-leq-concat-base-2" m).bind (·.next? byEvaluate)
          | false, false => byEvaluate m
    | _, _ => none
  | _ => none

/-! ## Regular expressions -/

def reAllStar : Node := mkNode .REGEXP_STAR #[mkNode .REGEXP_ALLCHAR #[]]
def reNone : Node := mkNode .REGEXP_NONE #[]
def emptyRe : Node := mkNode .STRING_TO_REGEXP #[mkWord []]

/-- A certificate that `cur` rewrites to `target`, by a short search: `aci_norm`
or `absorb` directly, or after one of `ruleNames`. -/
partial def reach (rw : (m : Node) → Rw m) (ruleNames : List String) (target : Node) : Nat → (cur : Node) → Option (Rw cur)
  | 0, _ => none
  | fuel + 1, cur =>
    if cur == target then some (Rw.id cur) else
    firstOf [fun _ => aci cur target, fun _ => checkBy .absorb cur target,
      fun _ => (firstOf (ruleNames.map fun r _ => byRuleE rw r cur)).bind (·.next? (reach rw ruleNames target fuel))]

/-- cvc5's `rewriteAndOrRegExp`, its flattening part (`RE_ANDOR_FLATTEN`,
`RE_AND_EMPTY`, `RE_OR_ALL`, `RE_INTER_CONST_CONST_CONFLICT`). The macros
`rewriteViaMacroReInterUnionConstElim` and
`rewriteViaMacroReInterUnionInclusion` are not ported. -/
def rewriteAndOr (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
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
  reach rw ["re-union-all", "re-inter-all", "re-inter-cstring-neg"] target (n.getChildren.size + 2) n

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
def postRewrite (rw : (m : Node) → Rw m) (n : Node) : RewriteResponse n :=
  let r : Option (Rw n) := match n.getKind with
    | .STRING_CONCAT => rewriteConcat n
    | .STRING_LENGTH => rewriteLength rw n
    | .EQUAL => rewriteEquality n
    | .STRING_CHARAT => byRule "str-at-elim" n
    | .STRING_SUBSTR => rewriteSubstr rw n
    | .STRING_PREFIX | .STRING_SUFFIX => rewritePrefixSuffix rw n
    | .STRING_CONTAINS => rewriteContains rw n
    | .STRING_REPLACE => rewriteReplace rw n
    | .STRING_REPLACE_ALL => rewriteReplaceAll rw n
    | .STRING_INDEXOF => rewriteIndexof rw n
    | .STRING_REV => rewriteStrReverse n
    | .STRING_TO_LOWER | .STRING_TO_UPPER => rewriteStrConvert n
    | .STRING_STOI => rewriteStrToInt rw n
    | .STRING_LT => byRule "str-lt-elim" n
    | .STRING_LEQ => rewriteStringLeq n
    | .STRING_IS_DIGIT => byRule "str-is-digit-elim" n
    | .REGEXP_OPT => byRule "re-opt-elim" n
    | .REGEXP_PLUS => byRule "re-plus-elim" n
    | .REGEXP_DIFF => byRule "re-diff-elim" n
    | .REGEXP_REPEAT => byRule "re-repeat-elim" n
    | .REGEXP_RANGE => rewriteRange n
    | .REGEXP_ALL => byRule "re-all-elim" n
    | .REGEXP_UNION | .REGEXP_INTER => rewriteAndOr rw n
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
def TheoryRewriter.strings (rw : (m : Node) → Rw m) : TheoryRewriter where
  preRewrite := .done
  postRewrite := StringsRewriter.postRewrite rw

end Telos
