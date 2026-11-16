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
the regular expression eliminations, `rewriteConcatRegExp`,
`rewriteRangeRegExp`, `rewriteAndOrRegExp` (without the inclusion macro),
`rewriteStarRegExp`, most of `rewriteMembership`, and from `StringsRewriter` the conversions, `str.<`,
`str.<=` and `str.is_digit`; with the entailments they use (`ArithEntail`,
`StringsEntail`). Each case is certified by CPC rules, as cvc5 elaborates its
macros (see `docs/design.md`, roadmap item 8). Cases that are proof holes in
cvc5 and still have no CPC rule (`IDOF_NORM_PREFIX`, `REPL_SUBST_IDX`) are
left unchanged.

The strings rewriter is given the full rewriter (`rw`), which cvc5's
`StringsEntail::checkContains` uses, and which proves premises that evaluation
does not (`premiseProver`).

Not ported yet: `rewriteLoopRegExp`, inclusion and `RE_IN_DIST_CHAR_STAR` in
`rewriteMembership`, `IDOF_NORM_PREFIX`, the length of `str.to_lower` and
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

/-- `s` regrouped as the concatenation `g` of the same components, where `g`
may split a constant of `s` or add empty constants: by `aci_norm`, or by
rewriting `g` back to `s` (cvc5's `rewriteConcat`), reversed. -/
def regroup (s g : Node) : Option (Rw s) :=
  if s == g then some (Rw.id s) else
  (aci s g).orElse fun _ =>
    if g.getKind == .STRING_CONCAT then rewriteConcat g >>= Proof.reverse s else none

/-- cvc5's `StringsEntail::stripSymbolicLength`: strip components of `cs` from
the front (`front`) or the back while `curr` stays entailed non-negative after
subtracting their lengths. A constant is stripped whole when the constant lower
bound of `curr` is at least its length, and otherwise by that bound, which ends
the stripping. Returns the stripped components, the rest, and what is left of
`curr`. -/
def stripSymbolicLength (cs : List Node) (front : Bool) (curr : Node) :
    Option (List Node × List Node × Node) :=
  let zero := ArithEntail.zero
  let take (rest : List Node) := if front then rest.tail else rest.dropLast
  let add (stripped : List Node) (c : Node) := if front then stripped ++ [c] else c :: stripped
  let rec go (rest stripped : List Node) (curr : Node) (fuel : Nat) : List Node × List Node × Node :=
    match fuel, (if front then rest.head? else rest.getLast?) with
    | fuel + 1, some c =>
      if curr == zero then (stripped, rest, curr) else
      match word? c with
      | some w =>
        match ArithEntail.lowerBound? (ArithEntail.rewriteArith curr) with
        | some lb =>
          if lb ≤ 0 then (stripped, rest, curr)
          else if lb ≥ w.length then
            go (take rest) (add stripped c)
              (ArithEntail.rewriteArith (mkNode .SUB #[curr, .const (.integer w.length)])) fuel
          else
            -- strip `lb` characters of the constant, and stop
            let k := lb.toNat
            let (part, left) := if front then (w.take k, w.drop k) else (w.drop (w.length - k), w.take (w.length - k))
            let rest' := if front then mkWord left :: rest.tail else rest.dropLast ++ [mkWord left]
            (add stripped (mkWord part), rest',
              ArithEntail.rewriteArith (mkNode .SUB #[curr, .const (.integer lb)]))
        | none => (stripped, rest, curr)
      | none =>
        let next := ArithEntail.rewriteArith (mkNode .SUB #[curr, len c])
        if ArithEntail.check next then go (take rest) (add stripped c) next fuel
        else (stripped, rest, curr)
    | _, _ => (stripped, rest, curr)
  let (stripped, rest, curr) := go cs [] curr cs.length
  if stripped.isEmpty then none else some (stripped, rest, curr)

/-- cvc5's `rewriteViaMacroSubstrStripSymLength`, certified as cvc5 elaborates
`MACRO_SUBSTR_STRIP_SYM_LENGTH`: the string regrouped into the stripped part and
the rest (by `aci_norm`, or by splitting a constant: `regroup`), then
`str-substr-len-include-pre` or `str-substr-full` (`SS_LEN_INCLUDE`),
`str-substr-concat2` (`SS_STRIP_START_PT`) or `str-substr-len-include`
(`SS_STRIP_END_PT`), with their premises by `ArithEntail`. When everything is
stripped from the start, the result is empty: `str-substr-empty-start`. -/
def substrStripSymLength (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[s, i, l] =>
    let zero := ArithEntail.zero
    let cs := ArithEntail.concatChildren s
    -- Regroup `s` as `(str.++ first second)`, then apply `rule`.
    let regroupBy := fun (first second : List Node) (rule : String) =>
      if first.isEmpty || second.isEmpty then none else
      let g := mkNode .STRING_CONCAT #[mkConcat first, mkConcat second]
      (Rw.id n).next? (fun m => Rw.congrArg m 0 fun c => regroup c g) >>= fun r => r.next? (byRuleE rw rule)
    let lenInclude : Option (Rw n) :=
      if i == zero then
        match stripSymbolicLength cs true l with
        | some (stripped, rest, _) =>
          if rest.isEmpty then byRuleE rw "str-substr-full" n
          else regroupBy stripped rest "str-substr-len-include-pre"
        | none => none
      else none
    lenInclude.orElse fun _ =>
    -- `SS_STRIP_START_PT`
    (if i != zero then
      match stripSymbolicLength cs true i with
      | some (_, [], _) => byRuleE rw "str-substr-empty-start" n
      | some (stripped, rest, _) => regroupBy stripped rest "str-substr-concat2"
      | none => none
    else none).orElse fun _ =>
    -- `SS_STRIP_END_PT`
    if l != len s then
      let curr := ArithEntail.rewriteArith (mkNode .SUB #[len s, mkNode .ADD #[i, l]])
      match stripSymbolicLength cs false curr with
      | some (stripped, rest, _) => regroupBy rest stripped "str-substr-len-include"
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
def stripEndpoints (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
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
  -- Everything is stripped from a substring (of a `str.from_int`, which `b`
  -- cannot be in): cvc5 gets `(str.contains "" b)`, which is `false`; here
  -- `str-substr-ctn-contra`, the premise by the rewriter
  if isCtn && rem.isEmpty && a.getKind == .STRING_SUBSTR then
    return ← byRuleE rw "str-substr-ctn-contra" n
  -- A `str.from_int` endpoint, which `b` cannot start (end) in: one endpoint at a
  -- time, by `str-contains-strip-from-int-pre` (`-post`)
  if isCtn && (c1.getKind == .STRING_ITOS || c2.getKind == .STRING_ITOS) then
    return ← if c1.getKind == .STRING_ITOS then byRuleE rw "str-contains-strip-from-int-pre" n
      else byRuleE rw "str-contains-strip-from-int-post" n
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

/-- `CTN_LEN_INEQ`: `(str.contains a b)` is `false` when `|b| > |a|`, as
cvc5 proves it, through `(= a b)` being false (`str-eq-len-false`) and
`(str.contains a b)` being `(= a b)` (`str-contains-leq-len-eq`). cvc5 proves
the premise `(= (= (str.len a) (str.len b)) false)` by contradiction, in a
scope; Logos's checker takes only closed assumptions, and telos's terms have
free variables, so here it is `arith-eq-elim-int`, with the conjunct
`(>= (str.len a) (str.len b))` false by `(< (str.len a) (str.len b))`
(`ArithEntail`, `arith-elim-lt`) and `absorb`. -/
def ctnLenIneqCmds (n : Node) : Option (List Eo.CCmd) := do
  let #[a, b] := n.getChildren | none
  let la := len a
  let lb := len b
  let ltCmds ← ArithEntail.premiseProof (mkNode .LT #[la, lb]) tt
  let geqCmds ← ArithEntail.premiseProof (mkNode .GEQ #[lb, la]) tt
  let ge := mkNode .GEQ #[la, lb]
  let le := mkNode .LEQ #[la, lb]
  let ff := Node.const (.boolean false)
  let st := fun (r : Eo.CRule) (args : List Node) (prems : List Int) =>
    Eo.CCmd.step r (toArgList (args.map Node.toEo)) (prems.foldr .cons .nil)
  return ltCmds ++ [                                   -- (= (< la lb) true)
    st .arith_elim_lt [la, lb] [],                     -- (= (< la lb) (not (>= la lb)))
    st .symm [] [0],
    st .trans [] [0, 2],                               -- (= (not (>= la lb)) true)
    st .true_elim [] [0],
    st .false_intro [] [0],                            -- (= (>= la lb) false)
    st .arith_eq_elim_int [la, lb] [],                 -- (= (= la lb) (and (>= la lb) (<= la lb)))
    st .refl [le] [],
    st .nary_cong [mkNode .AND #[ge, le]] [2, 0],      -- (= (and …) (and false (<= la lb)))
    st .absorb [eqNode (mkNode .AND #[ff, le]) ff] [],
    st .trans [] [3, 1, 0],                            -- (= (= la lb) false)
    st .str_eq_len_false [a, b] [0]] ++                -- (= (= a b) false)
    geqCmds ++ [
    st .str_contains_leq_len_eq [a, b] [0],            -- (= (str.contains a b) (= a b))
    st .trans [] [0, Int.ofNat geqCmds.length + 1]]

@[inherit_doc ctnLenIneqCmds]
def ctnLenIneq (n : Node) : Option (Rw n) := do
  applyCmds ((← ctnLenIneqCmds n).foldr .cons .nil) n

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
        -- `CTN_SPLIT` for a constant first argument, one character at a time:
        -- `(or (= c b) (str.contains rest b))`, or `(or (= "" b) (= c b))` for
        -- the last (`str-contains-cnst-split-leq-one`, `str-contains-char`)
        else if ArithEntail.checkLengthOne b then
          match word? a with
          | some (c :: cs@(_ :: _)) => some do
            let r ← Rw.congrArg n 0 fun t => regroup t (mkNode .STRING_CONCAT #[mkWord [c], mkWord cs])
            r.next? (byRuleE rw "str-contains-cnst-split-leq-one")
          | _ => some (byRuleE rw "str-contains-char" n)
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
      fun _ => (stripEndpoints rw n).map some,
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
      -- `CTN_LEN_INEQ`
      fun _ => if ArithEntail.check2 lenB lenA true then
          some ((ctnLenIneq n).orElse fun _ => checkBy .str_ctn_multiset_subset n ff) else none,
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
            -- `CTN_REPL_LEN_ONE_TO_CTN`
            some ((byRuleE rw "str-contains-repl-self-tgt-leq-one" n).orElse fun _ =>
              byRuleE rw "str-contains-repl-self-tgt-char" n)
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
              -- `RPL_CCTN`: what is after the first match is pulled out (with
              -- the constants of the rest merged, as cvc5 does next)
              let target := mkConcat (replNode (mkConcat (concatNormChildren cc.mid)) b z :: cc.after)
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
      fun _ => if checkNonEmpty b then (stripEndpoints rw n).map some else none,
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

/-- The rule `r` with the given arguments, its premises `(= p true)` proven by
`premiseProver`, or for a premise `(p, true)` the equality `p` itself (as
`(= p true)`, then `true_elim`). -/
def byRuleProving (rw : (m : Node) → Rw m) (r : Eo.CRule) (args : List Node)
    (prems : List (Node × Bool)) (n : Node) : Option (Rw n) := do
  let blocks ← prems.mapM fun (p, isEq) => do
    let cs ← premiseProver rw p tt
    return if isEq then cs ++ [Eo.CCmd.step .true_elim .nil (.cons 0 .nil)] else cs
  let steps := blocks.flatten
  let ends := (blocks.scanl (fun k b => k + b.length) 0).tail
  let indices : Eo.CIndexList := ends.foldr (fun e acc => .cons (Int.ofNat (steps.length - e)) acc) .nil
  let ruleStep := Eo.CCmd.step r (toArgList (args.map Node.toEo)) indices
  applyCmds ((steps ++ [ruleStep]).foldr .cons .nil) n

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
    -- `IDOF_STRIP_CNST_ENDPTS`: a constant first component loses its first
    -- character, `(+ 1 (str.indexof …))` (`str-indexof-strip-char-pre`);
    -- otherwise what is stripped goes at once (cvc5's
    -- `(+ (str.len nb) (str.indexof …))`, not ported: it has no rule)
    let stripCnst : Option (Option (Rw n)) :=
      match stripConstantEndpoints children0 children1 1 with
      | some _ =>
        match children0 with
        | first :: rest =>
          match word? first with
          | some (c :: cs) =>
            if rest.isEmpty && cs.isEmpty then some none else
            let g := mkNode .STRING_CONCAT ((mkWord [c] :: (if cs.isEmpty then [] else [mkWord cs]) ++ rest).toArray)
            some do
              let r ← Rw.congrArg n 0 fun t => regroup t g
              r.next? (byRuleE rw "str-indexof-strip-char-pre")
          | _ => some none
        | [] => none
      | none => none
    -- `IDOF_STRIP_SYM_LEN` (`MACRO_STR_INDEXOF_STRIP_SYM_LENGTH`):
    -- `(+ (str.len s1) (str.indexof s2 b m))`, by `str-indexof-strip-prefix-len`
    -- when nothing is left of the index, otherwise `str-indexof-strip-sym-len`
    let stripSym : Option (Option (Rw n)) :=
      if !(ArithEntail.check z && ArithEntail.check2 len0 z) then none else
      match stripSymbolicLength children0 true z with
      | some (stripped, rest@(_ :: _), newLen) =>
        let s1 := mkConcat stripped
        let s2 := mkConcat rest
        some do
          let r ← Rw.congrArg n 0 fun c => regroup c (mkNode .STRING_CONCAT #[s1, s2])
          let r ← r.next? fun m =>
            (if newLen == zero then byRuleE rw "str-indexof-strip-prefix-len" m else none).orElse fun _ =>
            byRuleProving rw Eo.CRule.str_indexof_strip_sym_len [s1, s2, b, z, newLen]
              [(eqNode newLen (mkNode .SUB #[z, len s1]), true), (mkNode .GEQ #[newLen, zero], false),
               (mkNode .GEQ #[len s2, newLen], false),
               (ctnNode (mkNode .STRING_SUBSTR #[s2, newLen, len s2]) b, false)] m
          return r
      | _ => none
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
            fun _ => byRuleE rw "str-indexof-oob" n, fun _ => byRuleE rw "str-indexof-len" n])
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
              else stripCnst
            | none => stripCnst
          else stripSym
        | none => none,
      -- `RPL_PULL_ENDPT`
      fun _ => if z == zero then (stripEndpoints rw n).map some else none]
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
    -- `STR_LEQ_EVAL`, and `STR_LEQ_ID` for a constant (cvc5 proves both by
    -- evaluation)
    if a.isConst && b.isConst then byEvaluate n
    -- `STR_LEQ_ID`
    else if a == b then byRule "str-leq-id" n
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

/-- Whether a regular expression has no variables (cvc5's `isConstRegExp`). -/
def isConstRe (r : Node) : Bool := r.vars.isEmpty

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

/-- cvc5's `rewriteViaMacroReInterUnionConstElim` (`RE_ANDOR_CONST_REMOVE`):
a constant string `(str.to_re s)` of an intersection removes each constant
member `r` with `s` in `r`, or makes it empty when `s` is not in `r`; in a
union, `(str.to_re s)` is removed when `s` is in another constant member. Each
removal is one step of `re-inter-const-elim` (resp. `re-union-const-elim`), on
the node with `(str.to_re s)` and `r` moved to the front (`aci_norm`), and the
conflict is `re-inter-cstring-neg`. -/
def reInterUnionConstElim (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
  let nk := n.getKind
  let isInter := nk == .REGEXP_INTER
  let cs := n.getChildren.toList
  let isStr := fun (c : Node) => c.getKind == .STRING_TO_REGEXP
  let consts := cs.filter fun c => isConstRe c && isStr c
  let others := cs.filter fun c => isConstRe c && !isStr c
  if consts.isEmpty || others.isEmpty then none
  let mem := fun (c r : Node) =>
    let m := mkNode .STRING_IN_REGEXP #[c.getChildren[0]!, r]
    if (inReEval m tt).isSome then some true
    else if (inReEval m (.const (.boolean false))).isSome then some false else none
  -- cvc5's loop: the pairs `(c, r)` with `c` in `r`, or a conflicting constant
  -- string (`n` itself when a membership is not decided).
  let (pairs, conflict) := consts.foldl (init := (([] : List (Node × Node)), (none : Option Node)))
    fun (pairs, conflict) c =>
      if conflict.isSome then (pairs, conflict) else
      let (pairs, conflict, _) := others.foldl (init := (pairs, conflict, false))
        fun (pairs, conflict, done) r =>
          if conflict.isSome || done || (isInter && pairs.any (·.2 == r)) then (pairs, conflict, done) else
          match mem c r with
          | some true => (pairs ++ [(c, r)], none, !isInter)
          | some false => if isInter then (pairs, some c, done) else (pairs, conflict, done)
          | none => if isInter then (pairs, some n, done) else (pairs, conflict, done)
      (pairs, conflict)
  match conflict with
  | some c =>
    if c == n then none else
    let g := mkNode .REGEXP_INTER (#[c] ++ n.getChildren)
    (aci n g).bind (·.next? (byRuleE rw "re-inter-cstring-neg"))
  | none =>
    if pairs.isEmpty then none
    let removed := pairs.map fun (c, r) => if isInter then r else c
    let target := match cs.filter (!removed.contains ·) with
      | [c] => c
      | rest => mkNode nk rest.toArray
    let rule := if isInter then "re-inter-const-elim" else "re-union-const-elim"
    let step := fun (cr : Node × Node) (cur : Node) =>
      let rest := (cur.getChildren.toList.erase cr.1).erase cr.2
      let g := mkNode nk (#[cr.1, cr.2] ++ rest.toArray)
      (aci cur g).bind (·.next? (byRuleE rw rule))
    let rec go : List (Node × Node) → (cur : Node) → Option (Rw cur)
      | [], cur => aci cur target
      | cr :: crs, cur => (step cr cur).bind (·.next? (go crs))
    go pairs n

/-- cvc5's `rewriteAndOrRegExp`: flattening (`RE_ANDOR_FLATTEN`,
`RE_AND_EMPTY`, `RE_OR_ALL`, `RE_INTER_CONST_CONST_CONFLICT`), then
`reInterUnionConstElim`. The inclusion macro `rewriteViaMacroReInterUnionInclusion`
is not ported. -/
def rewriteAndOrFlatten (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
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
  reach rw ["re-union-all", "re-inter-all", "re-inter-const-const-conflict", "re-inter-cstring-neg"] target (n.getChildren.size + 2) n

def rewriteAndOr (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) :=
  (rewriteAndOrFlatten rw n).orElse fun _ =>
    reInterUnionConstElim rw n

/-- cvc5's `rewriteConcatRegExp`. `RE_CONCAT_EMPTY` is `absorb` and
`RE_CONCAT_FLATTEN` is `aci_norm`. The combinations of `RE_CONCAT` are taken one
rule at a time (the result is rewritten again): `re-concat-merge` for adjacent
strings, `re-concat-star-repeat` for adjacent equal stars, and
`re-concat-star-nullable1/2` for a constant nullable expression next to
`(re.* re.allchar)` (its premise by `str-in-re-eval` only, so only for constant
ones, as in cvc5). Then `re-concat-star-swap` (`RE_CONCAT_OPT`). -/
def rewriteConcatRe (n : Node) : Option (Rw n) :=
  let cs := n.getChildren.toList
  if cs.any (·.getKind == .REGEXP_NONE) then checkBy .absorb n reNone
  else if cs.any (fun c => c.getKind == .REGEXP_CONCAT || c == emptyRe) then
    let vec := cs.flatMap fun c =>
      if c.getKind == .REGEXP_CONCAT then c.getChildren.toList else if c == emptyRe then [] else [c]
    aci n (match vec with
      | [] => emptyRe
      | [c] => c
      | _ => mkNode .REGEXP_CONCAT vec.toArray)
  else
    let pairs := cs.zip cs.tail
    let isStr := fun (c : Node) => c.getKind == .STRING_TO_REGEXP
    let nullable := fun (c : Node) => isConstRe c && c != reAllStar
    let byEval := fun (name : String) =>
      rewriteByWith (fun p v => (inReEval p v).bind Proof.cmdsOf) name n
    firstOf [
      fun _ => if pairs.any (fun (a, b) => isStr a && isStr b) then byRule "re-concat-merge" n else none,
      fun _ => if pairs.any (fun (a, b) => a == b && a.getKind == .REGEXP_STAR) then
        byRule "re-concat-star-repeat" n else none,
      fun _ => if pairs.any (fun (a, b) => a == reAllStar && (nullable b || b == reAllStar)) then
        byEval "re-concat-star-nullable1" else none,
      fun _ => if pairs.any (fun (a, b) => b == reAllStar && nullable a) then
        byEval "re-concat-star-nullable2" else none,
      fun _ => if pairs.any (fun (a, b) => a.getKind == .REGEXP_STAR && a.getChildren[0]? == some b) then
        byRule "re-concat-star-swap" n else none]

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

/-- cvc5's `rewriteViaStrInReConsume`, certified by `str-in-re-consume`: the
result is computed by CPC's own `$str_re_consume`. -/
def inReConsume (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[x, r] => do
    let b ← Node.ofEo n.vars (Eo.__str_re_consume x.toEo r.toEo)
    if b == n then none
    checkBy .str_in_re_consume n b
  | _ => none

/-- cvc5's `rewriteMembership`, without inclusion
(`rewriteViaMacroStrInReInclusion`) and `RE_IN_DIST_CHAR_STAR`. -/
def rewriteMembership (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[x, r] =>
    let allchar := fun (c : Node) => c.getKind == .REGEXP_ALLCHAR
    let lenX := len x
    match r.getKind with
    | .REGEXP_NONE => byRule "re-in-empty" n
    | _ =>
    -- `RE_IN_EVAL`: a constant string in a regular expression without
    -- variables, or the empty string in a nullable (or not nullable) one
    let eval := fun (_ : Unit) =>
      (inReEval n (.const (.boolean true))).orElse fun _ => inReEval n (.const (.boolean false))
    if x.isConst && isConstRe r then eval ()
    else if word? x == some [] && (eval ()).isSome then eval ()
    else
    -- `none`: the case does not apply; `some none`: cvc5 stops here
    let byKind : Option (Option (Rw n)) := match r.getKind with
      | .REGEXP_ALLCHAR => some (byRule "re-in-sigma" n)
      | .REGEXP_STAR =>
        let body := r.getChildren[0]!
        match word? x with
        | some [] =>
          -- `RE_EMPTY_IN_STR_STAR`
          some (checkBy .str_in_re_eval n (.const (.boolean true)))
        | some [_] =>
          -- `RE_CHAR_IN_STR_STAR`
          if body.getKind == .STRING_TO_REGEXP then some (byRule "re-char-in-str-star" n)
          else if allchar body then some (byRule "re-in-sigma-star" n) else none
        | _ =>
          -- `RE_IN_DIST_CHAR_STAR`: when every string of `body` has length one,
          -- `(str.in_re (str.++ x₁ … xₙ) (re.* body))` is the conjunction of
          -- the `(str.in_re xᵢ (re.* body))` (`str-in-re-concat-star-char`;
          -- the length by CPC's own `$str_fixed_len_re`)
          if x.getKind == .STRING_CONCAT && Eo.__str_fixed_len_re body.toEo == .Numeral 1 then
            some (checkBy .str_in_re_concat_star_char n
              (mkNode .AND (x.getChildren.map fun c => mkNode .STRING_IN_REGEXP #[c, r])))
          else if allchar body then some (byRule "re-in-sigma-star" n)
          else if body.getKind == .REGEXP_CONCAT && body.getChildren.all allchar then
            -- `RE_IN_CHAR_MODULUS_STAR`
            let k := Node.const (.integer body.getChildren.size)
            some (checkBy .str_in_re_sigma_star n
              (mkNode .EQUAL #[mkNode .INTS_MODULUS #[lenX, k], .const (.integer 0)]))
          else none
      | .REGEXP_CONCAT =>
        let rcs := r.getChildren.toList
        let isAllStar := fun (c : Node) => c.getKind == .REGEXP_STAR && (c.getChildren[0]?.map allchar).getD false
        let consts := rcs.filter (·.getKind == .STRING_TO_REGEXP)
        if consts.length ≤ 1 && rcs.all (fun c => allchar c || isAllStar c || c.getKind == .STRING_TO_REGEXP) then
          if consts.isEmpty then
            -- `RE_CONCAT_PURE_ALLCHAR`
            let k := Node.const (.integer (rcs.filter allchar).length)
            some (checkBy .str_in_re_sigma n
              (mkNode (if rcs.any isAllStar then .GEQ else .EQUAL) #[lenX, k]))
          -- `RE_CONCAT_TO_CONTAINS`: (str.in_re x (re.++ _* "abc" _*))
          else if !rcs.any allchar && rcs.length ≥ 3 && rcs.head? != consts.head? && rcs.getLast? != consts.head? then
            some (byRule "str-in-re-contains" n)
          else none
        else none
      | .REGEXP_UNION => some (byRule "str-in-re-union-elim" n)
      | .REGEXP_INTER => some (byRule "str-in-re-inter-elim" n)
      | .STRING_TO_REGEXP => some (byRule "re-in-cstring" n)
      | .REGEXP_RANGE => if isConstRe r then some (byRule "str-in-re-range-elim" n) else none
      | .REGEXP_COMPLEMENT => some (byRule "re-in-comp" n)
      | _ => none
    match byKind with
    | some (some rw) => some rw
    | some none => none
    -- `RE_SIMPLE_CONSUME`
    | none => inReConsume n
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
    | .REGEXP_CONCAT => rewriteConcatRe n
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
