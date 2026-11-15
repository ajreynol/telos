import Telos.Strings.ArithEntail

/-!
# String entailments

A port of the parts of cvc5's `StringsEntail`
(`src/theory/strings/strings_entail.cpp`) that `rewriteContains` and its
neighbours use: component-wise containment, the stripping of constant
endpoints, and the multiset approximation. These only decide what a node
rewrites to; the strings rewriter certifies each result with CPC rules.

cvc5's `checkContains` rewrites `(str.contains a b)` with the full rewriter;
here it is a parameter (`Ctn`), which the strings rewriter gives.

Words are lists of code points, as in `Node.const (.string _)`.
-/

namespace Telos

namespace Word

/-- The first position at or after `start` where `t` occurs in `s`
(`String::find`). -/
def find (s t : List Nat) (start : Nat := 0) : Option Nat :=
  (List.range (s.length + 1)).find? fun i => i ≥ start && t.isPrefixOf (s.drop i)

/-- The last position where `t` occurs in `s` (`String::rfind`). -/
def rfind (s t : List Nat) : Option Nat :=
  (List.range (s.length + 1)).reverse.find? fun i => t.isPrefixOf (s.drop i)

def pre (s : List Nat) (k : Nat) : List Nat := s.take k
def suffix (s : List Nat) (k : Nat) : List Nat := s.drop (s.length - k)

/-- The longest suffix of `x` that is a prefix of `y` (`String::overlap`). -/
def overlap (x y : List Nat) : Nat :=
  ((List.range (min x.length y.length + 1)).reverse.find? fun i =>
    i > 0 && suffix x i == pre y i).getD 0

/-- The longest prefix of `x` that is a suffix of `y` (`String::roverlap`). -/
def roverlap (x y : List Nat) : Nat :=
  ((List.range (min x.length y.length + 1)).reverse.find? fun i =>
    i > 0 && pre x i == suffix y i).getD 0

/-- `Word::hasOverlap`. -/
def hasOverlap (x y : List Nat) (rev : Bool) : Bool :=
  !x.isEmpty && ((find x y).isSome || (if rev then roverlap x y else overlap x y) != 0)

/-- Whether the code point is a decimal digit. -/
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- `String::isNumber`: non-empty, all digits. -/
def isNumber (s : List Nat) : Bool := !s.isEmpty && s.all isDigit

end Word

namespace StringsEntail

open Node

/-- `utils::getConcat`. -/
def getConcat (n : Node) : List Node :=
  if n.getKind == .STRING_CONCAT then n.getChildren.toList else [n]

def word? : Node → Option (List Nat)
  | .const (.string cs) => some cs
  | _ => none

def mkWord (cs : List Nat) : Node := .const (.string cs)

/-- `utils::mkConcat`. -/
def mkConcat : List Node → Node
  | [] => mkWord []
  | [c] => c
  | cs => mkNode .STRING_CONCAT cs.toArray

/-- cvc5's `checkContains`: the value of `(str.contains a b)` after rewriting,
when it is a constant. -/
abbrev Ctn := Node → Node → Option Bool

/-- `componentContainsBase`: whether `n1` contains `n2` (as a suffix for
`dir = 1`, a prefix for `dir = -1`), with the remainders before and after when
`computeRemainder`. -/
def componentContainsBase (ctn : Ctn) (isExt : Bool) (n1 n2 : Node) (dir : Int)
    (computeRemainder : Bool) : Option (Option Node × Option Node) :=
  if n1 == n2 then some (none, none) else
  match word? n1, word? n2 with
  | some s1, some s2 =>
    let len1 := s1.length
    let len2 := s2.length
    if len2 < len1 then
      if dir == 1 then
        if Word.suffix s1 len2 == s2 then
          some (if computeRemainder then some (mkWord (Word.pre s1 (len1 - len2))) else none, none)
        else none
      else if dir == -1 then
        if Word.pre s1 len2 == s2 then
          some (none, if computeRemainder then some (mkWord (Word.suffix s1 (len1 - len2))) else none)
        else none
      else
        match Word.find s1 s2 with
        | some f =>
          if computeRemainder then
            some (if f > 0 then some (mkWord (Word.pre s1 f)) else none,
              if len1 > f + len2 then some (mkWord (Word.suffix s1 (len1 - (f + len2)))) else none)
          else some (none, none)
        | none => none
    else none
  | _, _ =>
    if !isExt || computeRemainder then none else
    -- n1 = x containing n2 = (str.substr x n m)
    let substrCase : Bool := match n2.getKind, n2.getChildren with
      | .STRING_SUBSTR, #[s, i, l] =>
        if s == n1 then
          if dir == 1 then ArithEntail.check2 (mkNode .ADD #[i, l]) (mkNode .STRING_LENGTH #[s])
          else if dir == -1 then i == ArithEntail.zero
          else true
        else false
      | _, _ => false
    if substrCase then some (none, none) else
    if dir == 0 then
      match n1.getKind, n1.getChildren with
      | .STRING_REPLACE, #[x, _, z] =>
        -- (str.contains (str.replace x y z) w) is true when x and z contain w
        if ctn x n2 == some true && ctn z n2 == some true then some (none, none) else none
      | _, _ => none
    else none

/-- The result of component-wise containment: the position, and with the
remainders computed, the components before, the matched components, and the
components after. -/
structure Components where
  index : Nat
  before : List Node
  mid : List Node
  after : List Node

/-- `componentContainsInternal`: whether the components `n2` occur in order in
the components `n1`. With `computeRemainder`, `n1` is split around the match
(`remainderDir` 1 keeps what is before in `mid`, -1 what is after). -/
def componentContains (ctn : Ctn) (isExt : Bool) (n1 n2 : List Node)
    (computeRemainder : Bool := false) (remainderDir : Int := 0) : Option Components :=
  let concat2 := fun a b => mkNode .STRING_CONCAT #[a, b]
  match n2 with
  | [m] =>
    (List.range n1.length).findSome? fun i =>
      (componentContainsBase ctn isExt n1[i]! m 0 computeRemainder).map fun (rb, re) =>
        if !computeRemainder then ⟨i, [], n1, []⟩ else
        -- n1[i] is replaced by m
        let n1 := n1.set i m
        let (n1, ne) :=
          if remainderDir != -1 then (n1.take (i + 1), re.toList ++ n1.drop (i + 1))
          else match re with
            | some e => (n1.set i (concat2 n1[i]! e), [])
            | none => (n1, [])
        let (n1, nb) :=
          if remainderDir != 1 then (n1.drop i, n1.take i ++ rb.toList)
          else match rb with
            | some b => (n1.set i (concat2 b n1[i]!), [])
            | none => (n1, [])
        ⟨i, nb, n1, ne⟩
  | m :: ms =>
    if n1.length < n2.length then none else
    let diff := n1.length - n2.length
    (List.range (diff + 1)).findSome? fun i =>
      match componentContainsBase ctn isExt n1[i]! m 1 (computeRemainder && remainderDir != 1) with
      | none => none
      | some (rbFirst, _) =>
        -- the inner components must be equal, and the last a prefix
        let k := ms.length
        let inner := (List.range (k - 1)).all fun j => n1[i + j + 1]! == ms[j]!
        if !inner then none else
        match componentContainsBase ctn isExt n1[i + k]! ms[k - 1]! (-1)
            (computeRemainder && remainderDir != -1) with
        | none => none
        | some (_, reLast) =>
          if !computeRemainder then some ⟨i, [], n1, []⟩ else
          let (n1, ne) :=
            if remainderDir != -1 then
              ((n1.take (i + k + 1)).set (i + k) ms[k - 1]!, reLast.toList ++ n1.drop (i + k + 1))
            else (n1, [])
          let (n1, nb) :=
            if remainderDir != 1 then
              let n1 := n1.set i m
              (n1.drop i, n1.take i ++ rbFirst.toList)
            else (n1, [])
          some ⟨i, nb, n1, ne⟩
  | [] => none

/-- `utils::decomposeSubstrChain`: the base of a chain of `str.substr`, and
whether there was one. -/
partial def substrBase (s : Node) : Node × Bool :=
  match s.getKind, s.getChildren with
  | .STRING_SUBSTR, #[b, _, _] => ((substrBase b).1, true)
  | _, _ => (s, false)

/-- One direction of `stripConstantEndpoints` (`r` 0: the front, 1: the back).
`none` when cvc5 returns `false` at once; otherwise the new state, and whether
everything was removed. -/
def stripOne (r : Nat) (n2 : List Node) :
    List Node × List Node × List Node × Bool → Option ((List Node × List Node × List Node × Bool) × Bool)
  | (n1, nb, ne, changed) =>
    let index0 := if r == 0 then 0 else n1.length - 1
    let index1 := if r == 0 then 0 else n2.length - 1
    let n1cmp0 := n1[index0]!
    if word? n1cmp0 == some [] then none else
    let (n1cmp, isSubstr) := substrBase n1cmp0
    let (remove, n1, nb, ne, changed) : Bool × List Node × List Node × List Node × Bool :=
      match word? n1cmp with
      | some s =>
        let slen := s.length
        let (remove, overlap) : Bool × Nat :=
          match word? n2[index1]! with
          | some t =>
            match (if r == 0 then Word.find s t else Word.rfind s t) with
            | none =>
              if n1.length == 1 then (true, slen)
              else if !isSubstr then (false, if r == 0 then Word.overlap s t else Word.overlap t s)
              else (false, slen)
            | some ret => if !isSubstr then (false, slen - ret) else (false, slen)
          | none => (false, slen)
        if overlap < slen then
          if overlap == 0 then (true, n1, nb, ne, true)
          else if r == 0 then
            (remove, n1.set index0 (mkWord (Word.suffix s overlap)), nb ++ [mkWord (Word.pre s (slen - overlap))], ne, true)
          else
            (remove, n1.set index0 (mkWord (Word.pre s overlap)), nb, mkWord (Word.suffix s (slen - overlap)) :: ne, true)
        else (remove, n1, nb, ne, changed)
      | none =>
        if n1cmp.getKind == .STRING_ITOS then
          match word? n2[index1]! with
          | some t =>
            if n1.length == 1 then (!Word.isNumber t, n1, nb, ne, changed)
            else
              let c := if r == 0 then t.head? else t.getLast?
              (!(c.map Word.isDigit).getD true, n1, nb, ne, changed)
          | none => (false, n1, nb, ne, changed)
        else (false, n1, nb, ne, changed)
    if remove then
      let (n1, nb, ne) :=
        if r == 0 then (n1.drop 1, nb ++ [n1[index0]!], ne)
        else (n1.dropLast, nb, n1[index0]! :: ne)
      some ((n1, nb, ne, true), n1.isEmpty)
    else some ((n1, nb, ne, changed), false)

/-- `stripConstantEndpoints`: strip the parts of the first (`dir` 1) or last
(`dir` -1) component of `n1`, or both (`dir` 0), that cannot overlap `n2`.
Returns what is stripped before, the rest, and what is stripped after, when
something is. -/
def stripConstantEndpoints (n1 n2 : List Node) (dir : Int) :
    Option (List Node × List Node × List Node) := do
  if n1.isEmpty || n2.isEmpty then none
  let st := (n1, [], [], false)
  let st ← if dir == 0 || dir == 1 then
      match stripOne 0 n2 st with
      | some (st', true) => return (st'.2.1, st'.1, st'.2.2.1)
      | some (st', false) => pure st'
      | none => none
    else pure st
  let st ← if dir == 0 || dir == -1 then
      match stripOne 1 n2 st with
      | some (st', _) => pure st'
      | none => none
    else pure st
  let (rest, nb, ne, changed) := st
  if changed then some (nb, rest, ne) else none

/-- `getMultisetApproximation`. -/
partial def multisetApprox (a : Node) : Node :=
  let a := (substrBase a).1
  match a.getKind, a.getChildren with
  | .STRING_REPLACE, #[x, _, z] => multisetApprox (mkNode .STRING_CONCAT #[x, z])
  | .STRING_CONCAT, cs => mkNode .STRING_CONCAT (cs.map multisetApprox)
  | _, _ => a

/-- `checkMultisetSubset`: whether `b` has more occurrences of some character
than `a` can have, the components of `a` that are not constants being in `b`
as often. -/
def checkMultisetSubset (a b : Node) : Bool :=
  let avec := getConcat (multisetApprox a)
  let bvec := getConcat b
  let count (v : List Node) (c : Node) := v.countP (· == c)
  let nconstOk := avec.all fun c => c.isConst || count avec c ≤ count bvec c
  if !nconstOk then false else
  let chars (v : List Node) : List Nat := v.flatMap fun c => (word? c).getD []
  let ca := chars avec
  let cb := chars bvec
  (ca ++ cb).any fun ch => ca.count ch < cb.count ch

end StringsEntail

end Telos
