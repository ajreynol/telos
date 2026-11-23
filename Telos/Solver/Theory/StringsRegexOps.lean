import Telos.Solver.Regex
import Telos.Rewriter.Rewrite

/-!
# Operations on regular expressions for the theory of strings

The parts of cvc5's `RegExpOpr` (`src/theory/strings/regexp_operation.cpp`) and
`RegExpEntail` (`regexp_entail.cpp`) that the regular expression solver uses,
on nodes, without state:
- whether a regular expression has no string variables (`isConstRegExp`,
  `getRegExpConstType`);
- whether it contains the empty string (`delta`);
- inclusion of the language of one in that of another (`regExpIncludes`), a
  syntactic test, with the membership of constant strings decided by the
  matcher of models (`TRe`, as Logos's semantics; cvc5 tests it by its own
  `testConstStringInRegExp`, which agrees);
- the positive unfolding of a membership (`reduceRegExpPos`): a membership in a
  concatenation is the string as a concatenation of components, each in its
  part (the purification skolems `@re_unfold_pos_component`, or the string of a
  `str.to_re`); one in a star is empty, in the body, or the concatenation of
  the body without the empty string, the star, and the body again.
-/

namespace Telos.Solver.Strings

open Telos

private def mk (k : Kind) (cs : Array Node) : Node := Node.mkNode k cs
private def word (w : List Nat) : Node := .const (.string w)

/-- `utils::isRegExpKind`. -/
def isRegExpKind (k : Kind) : Bool :=
  k == .REGEXP_NONE || k == .REGEXP_ALL || k == .REGEXP_ALLCHAR || k == .STRING_TO_REGEXP ||
    k == .REGEXP_CONCAT || k == .REGEXP_UNION || k == .REGEXP_INTER || k == .REGEXP_DIFF ||
    k == .REGEXP_STAR || k == .REGEXP_PLUS || k == .REGEXP_OPT || k == .REGEXP_RANGE ||
    k == .REGEXP_COMPLEMENT || k == .REGEXP_REPEAT || k == .REGEXP_LOOP

/-- `utils::isCharacterRange`. -/
def isCharacterRange : Node → Bool
  | .app (.kind .REGEXP_RANGE) #[.const (.string [_]), .const (.string [_])] => true
  | _ => false

/-- `RegExpEntail::isConstRegExp`: no variables (the strings of `str.to_re` are
constants, the ranges of characters). -/
partial def isConstRegExp (r : Node) : Bool :=
  match r with
  | .app (.kind .STRING_TO_REGEXP) #[c] => c.isConst
  | .app (.kind .REGEXP_RANGE) _ => isCharacterRange r
  | .app op cs =>
    let k := match op with
      | .kind k | .indexed k _ => some k
      | _ => none
    match k with
    | some k => isRegExpKind k && cs.all isConstRegExp
    | none => false
  | _ => false

/-- `RegExpConstType`: concrete constant (no `re.allchar`, ranges or
complements), constant, or with variables. -/
inductive ReConst where
  | concrete | constant | variable
  deriving DecidableEq, Inhabited

def ReConst.rank : ReConst → Nat
  | .concrete => 0 | .constant => 1 | .variable => 2

/-- `RegExpOpr::getRegExpConstType`. -/
partial def regExpConstType (r : Node) : ReConst :=
  match r with
  | .app (.kind .STRING_TO_REGEXP) #[c] => if (Telos.rewrite c).isConst then .concrete else .variable
  | .app (.kind .REGEXP_ALLCHAR) _ | .app (.kind .REGEXP_RANGE) _ => .constant
  | .app op cs =>
    let k := match op with
      | .kind k | .indexed k _ => some k
      | _ => none
    match k with
    | some k =>
      if !isRegExpKind k then .variable else
      cs.foldl (fun acc c => let t := regExpConstType c; if t.rank > acc.rank then t else acc)
        (if k == .REGEXP_COMPLEMENT then .constant else .concrete)
    | none => .variable
  | _ => .variable

/-- `RegExpOpr::checkConstRegExp`. -/
def checkConstRegExp (r : Node) : Bool := regExpConstType r != .variable

/-- The value of a constant regular expression (`isConstRegExp`), for the
membership of constant strings. -/
partial def toTRe (r : Node) : Option TRe :=
  match r with
  | .app (.kind .STRING_TO_REGEXP) #[.const (.string w)] => some (TRe.ofList w)
  | .app (.kind .REGEXP_NONE) #[] => some .empty
  | .app (.kind .REGEXP_ALL) #[] => some (.star .allchar)
  | .app (.kind .REGEXP_ALLCHAR) #[] => some .allchar
  | .app (.kind .REGEXP_RANGE) #[.const (.string a), .const (.string b)] => some (TRe.mkRange a b)
  | .app (.kind .REGEXP_CONCAT) cs => do
    let ts ← cs.toList.mapM toTRe
    return ts.foldr TRe.mkConcat .epsilon
  | .app (.kind .REGEXP_UNION) cs => do
    let ts ← cs.toList.mapM toTRe
    return ts.foldr TRe.mkUnion .empty
  | .app (.kind .REGEXP_INTER) cs => do
    let ts ← cs.toList.mapM toTRe
    return ts.foldr TRe.mkInter (.star .allchar)
  | .app (.kind .REGEXP_STAR) #[a] => return TRe.mkStar (← toTRe a)
  | .app (.kind .REGEXP_PLUS) #[a] => do let t ← toTRe a; return TRe.mkConcat t (TRe.mkStar t)
  | .app (.kind .REGEXP_OPT) #[a] => return TRe.mkUnion (← toTRe a) .epsilon
  | .app (.kind .REGEXP_COMPLEMENT) #[a] => return TRe.mkComp (← toTRe a)
  | .app (.kind .REGEXP_DIFF) #[a, b] => return TRe.mkInter (← toTRe a) (TRe.mkComp (← toTRe b))
  | .app (.indexed .REGEXP_REPEAT #[i]) #[a] => return (← toTRe a).exp i.toNat
  | .app (.indexed .REGEXP_LOOP #[i, j]) #[a] => return TRe.loop i j (← toTRe a)
  | _ => none

/-- `RegExpEntail::testConstStringInRegExp`. -/
def testConstStringInRegExp (w : List Nat) (r : Node) : Bool :=
  match toTRe r with
  | some t => TRe.inRe w t
  | none => false

/-- `RegExpOpr::delta`: whether `r` contains the empty string, `1` (yes), `2`
(no) or `0` (unknown, with the condition `exp` for it). -/
partial def delta (r : Node) : Nat × Option Node :=
  let (ret, exp) : Nat × Option Node := match r with
    | .app (.kind .REGEXP_NONE) _ | .app (.kind .REGEXP_ALLCHAR) _ | .app (.kind .REGEXP_RANGE) _ =>
      (2, none)
    | .app (.kind .STRING_TO_REGEXP) #[s] =>
      let tmp := Telos.rewrite s
      if tmp.isConst then (if tmp == word [] then (1, none) else (2, none))
      else
        let hasConst := match tmp with
          | .app (.kind .STRING_CONCAT) cs => cs.any (·.isConst)
          | _ => false
        if hasConst then (2, none) else (0, some (Node.eqNode s (word [])))
    | .app (.kind k) cs =>
      if k == .REGEXP_CONCAT || k == .REGEXP_UNION || k == .REGEXP_INTER then Id.run do
        let checkTmp := if k == .REGEXP_UNION then 1 else 2
        let retTmp := if k == .REGEXP_UNION then 2 else 1
        let mut vec : Array Node := #[]
        for c in cs do
          let (t, e) := delta c
          if t == checkTmp then return (checkTmp, none)
          if t == 0 then if let some e := e then vec := vec.push e
        if vec.isEmpty then return (retTmp, none)
        let kr := if k == .REGEXP_UNION then Kind.OR else .AND
        return (0, some (if vec.size == 1 then vec[0]! else mk kr vec))
      else if k == .REGEXP_STAR || k == .REGEXP_OPT then (1, none)
      else if k == .REGEXP_PLUS then delta cs[0]!
      else if k == .REGEXP_COMPLEMENT then
        let (t, e) := delta cs[0]!
        (if t == 0 then 0 else 3 - t, e.map Node.notNode)
      else (0, none)
    | .app (.indexed .REGEXP_LOOP #[lo, _]) #[a] => if lo == 0 then (1, none) else delta a
    | _ => (0, none)
  (ret, exp.map (Telos.rewrite ·))

/-- `utils::getRegexpComponents`. -/
partial def regexpComponents (r : Node) : Array Node :=
  match r with
  | .app (.kind .REGEXP_CONCAT) cs => cs.foldl (fun acc c => acc ++ regexpComponents c) #[]
  | .app (.kind .STRING_TO_REGEXP) #[.const (.string w)] =>
    w.toArray.map fun c => mk .STRING_TO_REGEXP #[word [c]]
  | _ => #[r]

def sigmaStar : Node := mk .REGEXP_STAR #[mk .REGEXP_ALLCHAR #[]]

/-- `utils::isUnboundedWildcard`. -/
def isUnboundedWildcard (rs : Array Node) (start : Nat) : Bool := Id.run do
  let mut i := start
  while i < rs.size && rs[i]!.getKind == .REGEXP_ALLCHAR do i := i + 1
  if i >= rs.size then return false
  return rs[i]! == sigmaStar

/-- `RegExpEntail::regExpIncludes`: the language of `r₁` includes that of
`r₂` (sound, incomplete), with a cache. -/
partial def regExpIncludesC (r₁ r₂ : Node) : StateM (Std.HashMap (Key × Key) Bool) Bool := do
  if r₁ == r₂ then return true
  let key := (Key.mk r₁, Key.mk r₂)
  if let some b := (← get).get? key then return b
  let k₂ := r₂.getKind
  if k₂ == .STRING_TO_REGEXP then
    let ret := match r₂.getChildren with
      | #[.const (.string w)] => isConstRegExp r₁ && testConstStringInRegExp w r₁
      | _ => false
    modify (·.insert key ret)
    return ret
  let k₁ := r₁.getKind
  let mut ret := false
  let mut retSet := false
  if k₁ == .REGEXP_UNION then
    retSet := true
    for r in r₁.getChildren do
      if ← regExpIncludesC r r₂ then
        ret := true
        break
  if k₂ == .REGEXP_INTER && !ret then
    retSet := true
    for r in r₂.getChildren do
      if ← regExpIncludesC r₁ r then
        ret := true
        break
  if k₁ == .REGEXP_STAR then
    retSet := true
    let b := r₁.getChildren[0]!
    if b.getKind == .REGEXP_ALLCHAR then ret := true
    else ret ← regExpIncludesC b (if k₂ == .REGEXP_STAR then r₂.getChildren[0]! else r₂)
  else if k₁ == .STRING_TO_REGEXP then retSet := true
  else if k₁ == .REGEXP_RANGE && isCharacterRange r₁ then
    retSet := true
    if k₂ == .REGEXP_RANGE && isCharacterRange r₂ then
      match r₁.getChildren, r₂.getChildren with
      | #[.const (.string [l₁]), .const (.string [u₁])], #[.const (.string [l₂]), .const (.string [u₂])] =>
        ret := l₁ ≤ l₂ && l₂ ≤ u₁ && l₁ ≤ u₂ && u₂ ≤ u₁
      | _, _ => pure ()
  if retSet then
    modify (·.insert key ret)
    return ret
  -- avoid infinite loops
  modify (·.insert key false)
  let v₁ := regexpComponents r₁
  let v₂ := regexpComponents r₂
  let mut newIdxs : Array Nat := #[0]
  for n₂ in v₂ do
    let mut idxs : Array Nat := #[]
    for idx in newIdxs do
      if idx < v₁.size then
        if !idxs.contains idx then idxs := idxs.push idx
        if idx + 1 < v₁.size && v₁[idx]! == sigmaStar && !idxs.contains (idx + 1) then
          idxs := idxs.push (idx + 1)
    newIdxs := #[]
    for idx in idxs do
      if ← regExpIncludesC v₁[idx]! n₂ then
        if !newIdxs.contains (idx + 1) then newIdxs := newIdxs.push (idx + 1)
      if v₁[idx]! == sigmaStar then
        if !newIdxs.contains idx then newIdxs := newIdxs.push idx
      else if isUnboundedWildcard v₁ idx then
        if !newIdxs.contains idx then newIdxs := newIdxs.push idx
    if newIdxs.isEmpty then break
  let result := newIdxs.any fun idx => idx == v₁.size || (idx + 1 == v₁.size && v₁[idx]! == sigmaStar)
  modify (·.insert key result)
  return result

def regExpIncludes (r₁ r₂ : Node) : Bool := ((regExpIncludesC r₁ r₂).run {}).1

/-- The component skolem `i` of the unfolding of `(str.in_re s r)`. -/
def unfoldComponent (s r : Node) (i : Nat) : Node :=
  .skolem .RE_UNFOLD_POS_COMPONENT #[s, r, .const (.integer i)]

/-- `RegExpOpr::reduceRegExpPos`: the conclusion of the positive unfolding of
`mem`, `(str.in_re s r)`, for `r` a concatenation or a star; else none. -/
partial def reduceRegExpPos (mem : Node) : Option Node :=
  match mem with
  | .app (.kind .STRING_IN_REGEXP) #[s, r] =>
    match r with
    | .app (.kind .REGEXP_CONCAT) cs => Id.run do
      let mut sks : Array Node := #[]
      let mut nvec : Array Node := #[]
      for h : i in [0:cs.size] do
        match cs[i] with
        | .app (.kind .STRING_TO_REGEXP) #[b] => sks := sks.push b
        | c =>
          let sk := unfoldComponent s r i
          sks := sks.push sk
          nvec := nvec.push (mk .STRING_IN_REGEXP #[sk, c])
      let lem := Node.eqNode s (mk .STRING_CONCAT sks)
      let all := #[lem] ++ nvec
      return some (if all.size == 1 then all[0]! else mk .AND all)
    | .app (.kind .REGEXP_STAR) #[b] => do
      let emp := word []
      let se := Node.eqNode s emp
      let sinr := mk .STRING_IN_REGEXP #[s, b]
      let rd := mk .REGEXP_DIFF #[b, mk .STRING_TO_REGEXP #[emp]]
      let reExpand := mk .REGEXP_CONCAT #[rd, r, rd]
      let sinRExp ← reduceRegExpPos (mk .STRING_IN_REGEXP #[s, reExpand])
      return mk .OR #[se, sinr, sinRExp]
    | _ => none
  | _ => none

end Telos.Solver.Strings
