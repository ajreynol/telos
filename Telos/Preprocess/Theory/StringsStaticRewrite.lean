import Telos.Rewriter.Rewrite
import Telos.Rewriter.Theory.Strings

/-!
# Static rewriting of string equalities

cvc5's `TheoryStrings::ppStaticRewrite` of an equality of strings, which is
`SequencesRewriter::rewriteStrEqualityExt`
(`src/theory/strings/sequences_rewriter.cpp`). cvc5 justifies it by a trusted
step (`STRINGS_PP_STATIC_REWRITE`) that its proof reconstruction elaborates;
telos certifies each case by CPC rules:

* `EQ_NCTN`: `(= x y)` is `false` when `(str.contains x y)` or
  `(str.contains y x)` rewrites to `false` (`str-eq-ctn-full-false2`, `…1`);
* `EQ_NFIX`: `false` when the two sides have different constant prefixes or
  suffixes, after equal components; `STR_EQ_UNIFY`: equal components and the
  common parts of constants at the ends are removed. Both are certified by
  splitting the constants at the ends so that the components align (`regroup`),
  then `str-concat-unify`, `str-concat-clash` and their variants;
* the `str.replace` cases: `STR_EMP_REPL_X_Y_X`, `STR_EMP_REPL_EMP` (both
  forms), `STR_EQ_REPL_EMP`, `STR_EQ_REPL_TO_EQ`, `STR_EQ_REPL_NOT_CTN` and
  `STR_EQ_REPL_TO_DIS`, each a `str-eq-repl-*` rule.

Not ported: the `str.substr` cases (`STR_EMP_SUBSTR_*`, no CPC rule), and the
length-based unifications (`rewriteViaStrEqLenUnifyPrefix`,
`rewriteViaStrEqLenUnify`). Regular expression equalities (`RE_EQ_ELIM`) are
not ported either.
-/

namespace Telos.Preprocess

open Node StringsRewriter

/-- The full rewriter, which cvc5's entailment checks use. -/
def strRw : (m : Node) → Rw m := rewriteCert

/-- `EQ_NCTN`, in the direction `r`: `(str.contains node[r] node[1-r])`,
rewritten by `rewriteContains` (twice if it stays a containment), is `false`. -/
def eqNctn (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  firstOf ([0, 1].map fun r _ => do
    let (x, y) := if r == 0 then (a, b) else (b, a)
    let c := ctnNode x y
    let res := match rewriteContains strRw c with
      | some r₁ =>
        if r₁.1 != c && r₁.1.getKind == .STRING_CONTAINS then
          ((rewriteContains strRw r₁.1).map (·.1)).getD r₁.1
        else r₁.1
      | none => c
    if res != mkFalse then none
    byRuleE strRw (if r == 0 then "str-eq-ctn-full-false2" else "str-eq-ctn-full-false1") n)

/-- The components `c₀` and `c₁` of two concatenations, with the constants at
the front (or the back, `back`) split so that the components align: while the
components at the current position are equal, or are both constants, the
longer constant is split at the length of the shorter. Stops at the first
other pair. -/
def alignEnds (c₀ c₁ : List Node) (back : Bool) : List Node × List Node :=
  let rec go : Nat → List Node → List Node → List Node × List Node
    | 0, xs, ys => (xs, ys)
    | fuel + 1, x :: xs, y :: ys =>
      if x == y then let (xs', ys') := go fuel xs ys; (x :: xs', y :: ys') else
      match word? x, word? y with
      | some s, some t =>
        if s.length == t.length then (x :: xs, y :: ys)
        else
          let k := min s.length t.length
          let piece (w : List Nat) := if back then w.drop (w.length - k) else w.take k
          let rest (w : List Nat) := if back then w.take (w.length - k) else w.drop k
          if s.length > t.length then
            let (xs', ys') := go fuel (mkWord (rest s) :: xs) ys
            (mkWord (piece s) :: xs', y :: ys')
          else
            let (xs', ys') := go fuel xs (mkWord (rest t) :: ys)
            (x :: xs', mkWord (piece t) :: ys')
      | _, _ => (x :: xs, y :: ys)
    | _, xs, ys => (xs, ys)
  let fuel := c₀.length + c₁.length + 2
  if back then
    let (xs, ys) := go fuel c₀.reverse c₁.reverse
    (xs.reverse, ys.reverse)
  else go fuel c₀ c₁

/-- The equality `n` of two concatenations with their constants split at both
ends (`alignEnds`), as a certified rewrite. -/
def alignEquality (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let (c₀, c₁) := alignEnds (StringsEntail.getConcat a) (StringsEntail.getConcat b) false
  let (c₀, c₁) := alignEnds c₀ c₁ true
  let a' := mkConcat c₀
  let b' := mkConcat c₁
  let r ← Rw.congrArg n 0 fun c => regroup c a'
  r.next? fun m => Rw.congrArg m 1 fun c => regroup c b'

/-- The rules that unify or clash the ends of two concatenations. -/
def unifyRules : List String :=
  ["str-concat-unify", "str-concat-unify-rev", "str-concat-unify-base",
   "str-concat-unify-base-rev", "str-concat-clash", "str-concat-clash-rev",
   "str-concat-clash2", "str-concat-clash2-rev", "eq-symm"]

/-- `n` rewritten to `target` by aligning the ends and unifying (`EQ_NFIX`,
`STR_EQ_UNIFY`). -/
def unifyTo (n target : Node) : Option (Rw n) := do
  let r ← alignEquality n
  let fuel := 2 * ((StringsEntail.getConcat (n.getChildren[0]!)).length +
    (StringsEntail.getConcat (n.getChildren[1]!)).length) + 6
  r.next? (reach strRw unifyRules target fuel)

/-- `EQ_NFIX`: two components at the same position from the front (or the
back), after equal ones, are constants that differ on their common length. -/
def eqNfix (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let c₀ := StringsEntail.getConcat a
  let c₁ := StringsEntail.getConcat b
  let clash (back : Bool) : Bool :=
    let rec go : List Node → List Node → Bool
      | x :: xs, y :: ys =>
        match word? x, word? y with
        | some s, some t =>
          let k := min s.length t.length
          let piece (w : List Nat) := if back then w.drop (w.length - k) else w.take k
          if piece s != piece t then true else if x == y then go xs ys else false
        | _, _ => if x == y then go xs ys else false
      | _, _ => false
    if back then go c₀.reverse c₁.reverse else go c₀ c₁
  if !(clash false || clash true) then none
  unifyTo n mkFalse

/-- `STR_EQ_UNIFY`: the equal components at the ends, and the common parts of
constants there, removed from both sides. -/
def strEqUnify (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let stype := a.typeHint
  if stype != some .string then none
  let c₀ := StringsEntail.getConcat a
  let c₁ := StringsEntail.getConcat b
  -- cvc5's loop: from the back, then (reversed) from the front
  let step (c₀ c₁ : List Node) (fromBack : Bool) : List Node × List Node × Bool :=
    let rec pop : Nat → List Node → List Node → Bool → List Node × List Node × Bool
      | 0, xs, ys, ch => (xs, ys, ch)
      | fuel + 1, xs, ys, ch =>
        match xs.getLast?, ys.getLast? with
        | some x, some y =>
          if x == y then pop fuel xs.dropLast ys.dropLast true
          else
            match word? x, word? y with
            | some s, some t =>
              let (larger, ls, ss) := if s.length > t.length then (0, s, t) else (1, t, s)
              let k := ss.length
              let fits := if fromBack then ls.drop (ls.length - k) == ss else ls.take k == ss
              if !fits then (xs, ys, ch) else
              let restL := mkWord (if fromBack then ls.take (ls.length - k) else ls.drop k)
              if larger == 0 then (xs.dropLast ++ [restL], ys.dropLast, true)
              else (xs.dropLast, ys.dropLast ++ [restL], true)
            | _, _ => (xs, ys, ch)
        | _, _ => (xs, ys, ch)
    pop (c₀.length + c₁.length + 1) c₀ c₁ false
  -- first from the back (the lists as they are), then from the front (reversed)
  let (d₀, d₁, ch₁) := step c₀ c₁ true
  let (e₀, e₁, ch₂) := step d₀.reverse d₁.reverse false
  if !(ch₁ || ch₂) then none
  let s₁ := mkConcat e₀.reverse
  let s₂ := mkConcat e₁.reverse
  if s₁ == a && s₂ == b then none
  unifyTo n (eqNode s₁ s₂)

/-- The `str.replace` cases, with the replacement as `node[i]` and the other
side `x` (`STR_EMP_REPL_*` when `x` is empty, then `STR_EQ_REPL_*`). Each rule
has the replacement on the left: for `i = 1`, `eq-symm` first. -/
def strEqReplace (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let empty := mkWord []
  firstOf ([0, 1].map fun i _ => do
    let (repl, x) := if i == 0 then (a, b) else (b, a)
    let .app (.kind .STRING_REPLACE) #[r₀, r₁, r₂] := repl | none
    let oriented : Rw n := if i == 0 then Rw.id n else (byRule "eq-symm" n).getD (Rw.id n)
    if oriented.1.getChildren[0]? != some repl then none
    let by_ (rule : String) (target : Option Node := none) : Option (Rw n) := do
      let r ← oriented.next? (byRuleE strRw rule)
      match target with
      | some t => if r.1 == t then some r else r.next? fun m => (byRule "eq-symm" m).filter (·.1 == t)
      | none => some r
    -- `(= "" (str.replace …))`
    if x == empty then
      if r₀ == r₂ then return ← by_ "str-eq-repl-self-emp"
      if checkNonEmpty r₂ then return ← by_ "str-eq-repl-emp-tgt-nemp"
      if ArithEntail.checkLengthOne r₁ true && r₂ == empty then
        return ← by_ "str-eq-repl-len-one-emp-prefix"
    if checkNonEmpty x && r₀ == empty then return ← by_ "str-eq-repl-nemp-src-emp"
    if r₀ == r₂ && x == r₁ then return ← by_ "str-eq-repl-self-src" (some (eqNode x r₀))
    if x == r₀ && (strRw (eqNode r₁ r₂)).1 == mkFalse then return ← by_ "str-eq-repl-no-change"
    if r₂ == x && ArithEntail.checkEq (len r₁) (len r₂) then return ← by_ "str-eq-repl-tgt-eq-len"
    none)

/-- `rewriteStrEqualityExt`, in cvc5's order of cases. -/
def strEqualityExt (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  if n.getKind != .EQUAL then none
  let isStrTerm (t : Node) : Bool := !t.isConst && t.getKind.theoryId == .THEORY_STRINGS
  if !(isStrTerm a || isStrTerm b) then none
  firstOf [fun _ => eqNctn n, fun _ => eqNfix n, fun _ => strEqUnify n, fun _ => strEqReplace n]

end Telos.Preprocess
