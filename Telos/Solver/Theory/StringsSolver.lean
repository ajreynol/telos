import Telos.Solver.Theory.Strings
import Telos.Solver.Theory.StringsRegexOps

/-!
# The full-effort check of the theory of strings

A port of the full-effort check of cvc5's `TheoryStrings` (`postCheck`, with its
`Strategy`), for word equations with lengths (Stage 9, stage 1 of
`docs/theory-engine-plan.md`):
- the inference manager (`InferenceManager`): inferences are conflicts (sent
  at once), facts (asserted to the equality engine) or lemmas, pending until
  the strategy's round ends (`doPending`);
- the base solver (`BaseSolver`): the congruence of terms modulo empty strings
  (`checkInit`), and the constants classes are entailed to be equal to
  (`checkConstantEquivalenceClasses`);
- the core solver (`CoreSolver`): cycles of concatenations (`checkCycles`),
  flat forms (`checkFlatForms`), normal forms and their unification
  (`checkNormalFormsEq`), disequalities (`checkNormalFormsDeq`) and length
  normalization (`checkLengthsEqc`).

The steps of later stages (extended functions, regular expressions, codes,
sequences) do nothing yet: a relevant term that needs them makes the check
incomplete (`State.incomplete`), and so does a looping word equation, which
needs regular expressions, and the cardinality of the alphabet, which is not
checked (it only matters for more than 196608 classes of one length).

cvc5 compares node ids in places (`std::map`s of nodes, the oldest variable of
a class): telos uses its approximation of them (`NodeOrder`). The arithmetic
entailment of `stringCheckEntailLen` is approximated by the rewriter. These
only decide which inference is made, as do the orders of iteration.
-/

namespace Telos.Solver.Strings

open EE

/-! ## Helpers -/

def chk : EEM Check := return (← st).chk

def modifyChk (f : Check → Check) : EEM Unit := modifyStrings fun s => { s with chk := f s.chk }

def inConflict : EEM Bool := return (← get).teConflict

/-- cvc5's node order, approximated (`NodeOrder`, with the nodes numbered
during solving). -/
def nodeLt (a b : Node) : EEM Bool := do
  let o := (← read).order
  return ({ o with fresh := (← get).freshIds } : NodeOrder).lt a b

/-- Sort nodes in node order (a `std::set` or the keys of a `std::map`). -/
def sortNodes (xs : Array Node) : EEM (Array Node) := do
  let o := (← read).order
  let o : NodeOrder := { o with fresh := (← get).freshIds }
  return xs.qsort fun a b => o.lt a b

/-- `TheoryState::areEqual`. -/
def areEq (a b : Node) : EEM Bool := do
  if a == b then return true
  if (← hasTerm a) && (← hasTerm b) then areEqual a b else return false

/-- `TheoryState::areDisequal`. -/
def areDiseq (a b : Node) : EEM Bool := do
  if a == b then return false
  let mut isConst := true
  let mut hasTerms := true
  let mut a := a
  let mut b := b
  if ← hasTerm a then
    a ← rep a
    isConst := a.isConst
  else if !a.isConst then return false
  else hasTerms := false
  if ← hasTerm b then
    b ← rep b
    isConst := isConst && b.isConst
  else if !b.isConst then return false
  else hasTerms := false
  if isConst then return a != b
  if !hasTerms then return false
  areDisequal a b false

/-- The classes of the engine, from index `i`: the first representative at or
after `i`, and its index (`EqClassesIterator`). -/
def nextClass (i : Nat) : EEM (Option (Nat × Node)) := do
  let s ← get
  let mut j := i
  while j < s.nodes.size do
    if find s j == j && !s.isInternal[j]! then return some (j, s.nodes[j]!)
    j := j + 1
  return none

/-- The terms of a class (`EqClassIterator`), from its representative. -/
def classTerms (r : Node) : EEM (Array Node) := do
  let s ← get
  let some i := s.nodeIds.get? ⟨r⟩ | return #[r]
  let mut out := #[]
  let mut j := i
  repeat
    if !s.isInternal[j]! then out := out.push s.nodes[j]!
    j := s.enodes[j]!.next
    if j == i then break
  return out

/-- The negation of a literal (`Node::negate`). -/
def negLit (l : Node) : Node :=
  match l with
  | .app (.kind .NOT) #[a] => a
  | _ => Node.notNode l

/-- `utils::mkAnd`: without duplicates. -/
def mkAndU (xs : Array Node) : Node :=
  let u := xs.foldl (fun a x => if a.contains x then a else a.push x) #[]
  if u.isEmpty then Node.mkTrue else if u.size == 1 then u[0]! else Node.mkNode .AND u

/-- `NodeManager::mkAnd`. -/
def mkAndN (xs : Array Node) : Node :=
  if xs.isEmpty then Node.mkTrue else if xs.size == 1 then xs[0]! else Node.mkNode .AND xs

/-- `utils::mkConcat`. -/
def mkConcatA (cs : Array Node) : Node :=
  if cs.size == 1 then cs[0]! else if cs.isEmpty then emptyWord else Node.mkNode .STRING_CONCAT cs

/-- `TermRegistry::mkNConcat`. -/
def mkNConcat (cs : Array Node) : EEM Node := rw (mkConcatA cs)

def wordLen (n : Node) : Nat := ((word? n).getD []).length

def mkWord (w : List Nat) : Node := .const (.string w)

/-- `Word::substr`. -/
def wordSubstr (n : Node) (i : Nat) (len : Option Nat := none) : Node :=
  let w := (word? n).getD []
  let w := w.drop i
  mkWord (match len with | some l => w.take l | none => w)

/-- `Word::find`: the first index at or after `start` where `y` occurs in
`x`. -/
def wordFind (x y : List Nat) (start : Nat := 0) : Option Nat := Id.run do
  if x.length < y.length + start then return none
  for i in [start : x.length - y.length + 1] do
    if (x.drop i).take y.length == y then return some i
  return none

/-- `Word::rfind`: the first index from the end where `y` occurs in `x`
(counted from the end). -/
def wordRFind (x y : List Nat) : Option Nat :=
  (wordFind x.reverse y.reverse)

/-- `String::overlap`: the longest suffix of `x` that is a prefix of `y`. -/
def wordOverlap (x y : List Nat) : Nat := Id.run do
  let mut i := min x.length y.length
  while i > 0 do
    if x.drop (x.length - i) == y.take i then return i
    i := i - 1
  return 0

/-- `String::roverlap`: the longest prefix of `x` that is a suffix of `y`. -/
def wordROverlap (x y : List Nat) : Nat := Id.run do
  let mut i := min x.length y.length
  while i > 0 do
    if x.take i == y.drop (y.length - i) then return i
    i := i - 1
  return 0

/-- `Word::strncmp`, `Word::rstrncmp`. -/
def wordNcmp (x y : List Nat) (n : Nat) (isRev : Bool) : Bool :=
  if isRev then x.reverse.take n == y.reverse.take n else x.take n == y.take n

/-- `Word::splitConstant`: the remainder of the longer of `x` and `y` after
the shorter, if it is a prefix (suffix) of it. -/
def splitConstant (x y : Node) (isRev : Bool) : Option Node :=
  let wx := (word? x).getD []
  let wy := (word? y).getD []
  let short := min wx.length wy.length
  if !wordNcmp wx wy short isRev then none else
  let l := if wx.length <= wy.length then wy else wx
  some (mkWord (if isRev then l.take (l.length - short) else l.drop short))

/-- `utils::getSufficientNonEmptyOverlap`. -/
def sufficientNonEmptyOverlap (c d : Node) (isRev : Bool) : Nat :=
  let cw := (word? c).getD []
  let dw := (word? d).getD []
  let cLen := cw.length
  let (p, p2) := if isRev then
      let c1 := cw.take (cLen - 1)
      (cLen - wordROverlap c1 dw, wordRFind c1 dw)
    else
      let c1 := cw.drop 1
      (cLen - wordOverlap c1 dw, wordFind c1 dw)
  match p2 with
  | none => p
  | some p2 => if p > p2 + 1 then p2 + 1 else p

/-- `StringsEntail::canConstantContainList`: the constant components of `l`
occur in order in `c` (the indices of the first and last, unused). -/
def canConstantContainList (c : Node) (l : Array Node) : Bool := Id.run do
  let cw := (word? c).getD []
  let mut pos := 0
  for x in l do
    if x.isConst then
      match wordFind cw ((word? x).getD []) pos with
      | none => return false
      | some p => pos := p + wordLen x
  return true

/-- `SolverState::getLengthExp`. -/
def getLengthExp (t : Node) (exp : Array Node) (te : Node) (minExp : Bool := true) :
    EEM (Node × Array Node) := do
  if minExp then
    let lt ← rw (mkLen te)
    if ← hasTerm lt then return (lt, exp)
  let lengthTerm := match (← st).getEqcInfo? t with
    | some { lengthTerm := some l, .. } => match l with
      | .app (.kind .STRING_LENGTH) #[a] => a
      | _ => te
    | _ => te
  let exp := if te != lengthTerm then exp.push (Node.eqNode te lengthTerm) else exp
  return (← rw (mkLen lengthTerm), exp)

def getLength (t : Node) (exp : Array Node) (minExp : Bool := true) : EEM (Node × Array Node) :=
  getLengthExp t exp t minExp

/-- `SolverState::explainNonEmpty`. -/
def explainNonEmpty (s : Node) : EEM (Option Node) := do
  if ← areDiseq s emptyWord then return some (Node.notNode (Node.eqNode s emptyWord))
  let sLen ← rw (mkLen s)
  if ← areDiseq sLen (intConst 0) then return some (Node.notNode (Node.eqNode sLen (intConst 0)))
  return none

/-- `SolverState::isEqualEmptyWord`. -/
def isEqualEmptyWord (s : Node) : EEM (Option Node) := do
  let sr ← rep s
  if sr.isConst && wordLen sr == 0 && (word? sr).isSome then return some sr
  return none

/-! ## Skolems (`SkolemCache`, in terms of purification skolems) -/

def mkSubstr (t i l : Node) : Node := Node.mkNode .STRING_SUBSTR #[t, i, l]
def mkSub (a b : Node) : Node := Node.mkNode .SUB #[a, b]
/-- `utils::mkPrefix`. -/
def mkPrefix (t n : Node) : Node := mkSubstr t (intConst 0) n
/-- `utils::mkSuffix`. -/
def mkSuffix (t n : Node) : Node := mkSubstr t n (mkSub (mkLen t) n)
/-- `utils::mkSuffixOfLen`. -/
def mkSuffixOfLen (t n : Node) : Node := mkSubstr t (mkSub (mkLen t) n) n

/-- The purification skolem of the rewrite of `t`. -/
def purifyOf (t : Node) : EEM Node := do
  let k := Node.mkPurifySkolem (← rw t)
  note (.skolem k)
  return k

/-- `SK_PREFIX(x, n)`. -/
def skPrefix (x n : Node) : EEM Node := do purifyOf (mkPrefix (← rw x) (← rw n))
/-- `SK_SUFFIX_REM(x, n)`. -/
def skSuffixRem (x n : Node) : EEM Node := do purifyOf (mkSuffix (← rw x) (← rw n))

/-- `SK_ID_V_UNIFIED_SPT(_REV)(x, y)`. -/
def skUnifiedSpt (x y : Node) (isRev : Bool) : EEM Node := do
  let x ← rw x
  let y ← rw y
  let la := mkLen x
  let lb := mkLen y
  let ta := if isRev then mkPrefix x (mkSub la lb) else mkSuffix x lb
  let tb := if isRev then mkPrefix y (mkSub lb la) else mkSuffix y la
  purifyOf (Node.mkNode .ITE #[Node.mkNode .GEQ #[la, lb], ta, tb])

/-- `utils::getConcatConclusion` for `CONCAT_SPLIT` (`lprop = false`) and
`CONCAT_LPROP`: the conclusion and its skolem. -/
def concatSplitConclusion (x y : Node) (isRev lprop : Bool) : EEM (Node × Node) := do
  let sk ← skUnifiedSpt x y isRev
  let cc (b : Node) := if isRev then Node.mkNode .STRING_CONCAT #[sk, b] else Node.mkNode .STRING_CONCAT #[b, sk]
  let eq1 := Node.eqNode x (cc y)
  let conc := if lprop then eq1 else Node.mkNode .OR #[eq1, Node.eqNode y (cc x)]
  let conc := Node.mkNode .AND #[conc, Node.notNode (Node.eqNode sk emptyWord),
    Node.mkNode .GT #[mkLen sk, intConst 0]]
  return (conc, sk)

/-- `utils::getConcatConclusion` for `CONCAT_CSPLIT`. -/
def concatCSplitConclusion (x y : Node) (isRev : Bool) : EEM (Node × Node) := do
  let yw := (word? y).getD []
  let firstChar := if yw.length == 1 then y else mkWord (if isRev then yw.drop (yw.length - 1) else yw.take 1)
  let sk ← if isRev then skPrefix x (mkSub (mkLen x) (intConst 1)) else skSuffixRem x (intConst 1)
  let conc := Node.eqNode x (if isRev then Node.mkNode .STRING_CONCAT #[sk, firstChar]
    else Node.mkNode .STRING_CONCAT #[firstChar, sk])
  return (conc, sk)

/-- `utils::getConcatConclusion` for `CONCAT_CPROP`: `z ++ d` (in the direction)
against the constant `c`. -/
def concatCPropConclusion (z d c : Node) (isRev : Bool) : EEM (Node × Node) := do
  let p := sufficientNonEmptyOverlap c d isRev
  let rp := intConst p
  let preC := if isRev then mkSuffixOfLen c rp else mkPrefix c rp
  -- `SK_ID_C_SPT(z, preC)`: `SK_SUFFIX_REM(z, len(preC))`; reversed,
  -- `SK_PREFIX(z, len(z) - len(preC))`
  let sk ← if isRev then skPrefix z (mkSub (mkLen z) (mkLen preC)) else skSuffixRem z (mkLen preC)
  let conc := Node.eqNode z (if isRev then Node.mkNode .STRING_CONCAT #[sk, preC]
    else Node.mkNode .STRING_CONCAT #[preC, sk])
  return (conc, sk)

/-- `utils::getDecomposeConclusion`: `x = k1 ++ k2` with the length of `k1` (of
`k2`, reversed) `l`. -/
def decomposeConclusion (x l : Node) (isRev : Bool) : EEM (Node × Node × Node) := do
  let n := if isRev then mkSub (mkLen x) l else l
  let sk1 ← skPrefix x n
  let sk2 ← skSuffixRem x n
  let conc := Node.eqNode x (Node.mkNode .STRING_CONCAT #[sk1, sk2])
  let lc := Node.eqNode (mkLen (if isRev then sk2 else sk1)) l
  return (Node.mkNode .AND #[conc, lc], sk1, sk2)

/-! ## The inference manager -/

/-- `addToExplanation`: `(= a b)` unless they are the same, with a constant on
the right. -/
def addToExplanation (a b : Node) (exp : Array Node) : Array Node :=
  if a == b then exp else
  let (a, b) := if a.isConst && !b.isConst then (b, a) else (a, b)
  exp.push (Node.eqNode a b)

/-- The explanation of the premises, as the equality engine explains them
(`ProofEqEngine::explainVecWithProof`): those of `noExplain` as they are,
the others explained, in order, without duplicates; the conjunctions of the
reasons of internal facts split (`mkScope`). -/
def explainPremises (exp noExplain : Array Node) : EEM (Array Node) := do
  let mut out : Array Node := #[]
  for e in exp do
    if e == Node.mkTrue then continue
    if noExplain.contains e then
      if !out.contains e then out := out.push e
      continue
    for a in ← explainLit e do
      out := flattenAnd a out
  return out.filter (· != Node.mkTrue)

/-- `processConflict`: the conflict of the premises, explained, sent at once
(`trustedConflict`). -/
def processConflict (id : String) (premises : Array Node) : EEM Unit := do
  if ← inConflict then return
  let ps := premises.foldl (fun a p => flattenAnd p a) #[]
  let exp ← explainPremises ps #[]
  let conf := mkAndN exp
  modifyStrings fun s => { s with conflict := some (id, conf, ps) }
  note (.conflict stringsTheory id conf)
  modify fun s => { s with teConflict := true }

/-- `TermRegistry::removeProxyEqs`: the premises that are not trivial equalities
of a proxy variable and its term. -/
partial def removeProxyEqs (n : Node) (unproc : Array Node) : EEM (Array Node) := do
  match n with
  | .app (.kind .AND) cs =>
    let mut u := unproc
    for c in cs do u ← removeProxyEqs c u
    return u
  | _ =>
    let ns ← rw n
    if let .app (.kind .EQUAL) #[a, b] := ns then
      let pv := (← st).proxyVar
      for (x, y) in [(a, b), (b, a)] do
        if pv.contains ⟨x⟩ && pv.get? ⟨y⟩ == some x then return unproc
    if n == Node.mkTrue then return unproc
    return unproc.push n

/-- `InferInfo::isFact`: a literal of the theory of strings, with nothing
unexplained. -/
def isFact (ii : Inference) : Bool :=
  let atom := match ii.conc with
    | .app (.kind .NOT) #[a] => a
    | c => c
  !atom.isConst && Telos.theoryOf atom == .THEORY_STRINGS && ii.noExplain.isEmpty

/-- `InferenceManager::sendInference`: a conflict (sent now), a lemma or a fact
(pending). -/
def sendInferenceInfo (ii : Inference) (asLemma : Bool) : EEM Unit := do
  if ii.conc == Node.mkFalse && ii.noExplain.isEmpty then
    processConflict ii.id ii.exp
    return
  if asLemma || !isFact ii then
    modifyStrings fun s => { s with pendingLemmas := s.pendingLemmas.push ii }
    return
  -- `stringInferSym`: a fact whose premises are trivial is a lemma
  let mut unproc : Array Node := #[]
  for p in ii.exp do unproc ← removeProxyEqs p unproc
  if unproc.isEmpty then
    modifyStrings fun s => { s with pendingLemmas := s.pendingLemmas.push { id := ii.id, conc := ii.conc } }
    return
  modifyStrings fun s => { s with pendingFacts := s.pendingFacts.push ii }

/-- `sendInference(exp, noExplain, conc, id, isRev, asLemma)`: unless `conc`
rewrites to `true`. -/
def sendInference (exp : Array Node) (conc : Node) (id : String) (isRev : Bool := false)
    (asLemma : Bool := false) (noExplain : Array Node := #[]) : EEM Bool := do
  if conc != Node.mkFalse && (← rw conc) == Node.mkTrue then return false
  sendInferenceInfo { id, conc, exp, noExplain, idRev := isRev } asLemma
  return true

/-- `sendSplit`: `(or eq (not eq))` for the rewrite `eq` of `(= a b)`, unless it
is a constant, with the phase `preq` for `eq`. -/
def sendSplit (a b : Node) (id : String) (preq : Bool := true) : EEM Bool := do
  let eq ← rw (Node.eqNode a b)
  if eq.isConst then return false
  let ii : Inference := { id := id, conc := Node.mkNode .OR #[eq, Node.notNode eq] }
  modifyStrings fun s => { s with pendingPhases := s.pendingPhases.push (eq, preq) }
  modifyStrings fun s => { s with pendingLemmas := s.pendingLemmas.push ii }
  return true

def hasPending : EEM Bool := do
  let s ← st
  return !s.pendingFacts.isEmpty || !s.pendingLemmas.isEmpty

/-- `hasProcessed`: a conflict, or something pending. -/
def hasProcessed : EEM Bool := do return (← inConflict) || (← hasPending)

/-! ## The base solver (`BaseSolver`) -/

def baseInfo? (n : Node) : EEM (Option BaseEqcInfo) := return (← chk).baseInfo.get? ⟨n⟩

def setBaseInfo (n : Node) (b : BaseEqcInfo) : EEM Unit :=
  modifyChk fun c => { c with baseInfo := c.baseInfo.insert ⟨n⟩ b }

def isCongruent (n : Node) : EEM Bool := return (← st).congruent.contains ⟨n⟩

def addCongruent (n : Node) : EEM Unit := modifyStrings fun s => s.addCongruent n

/-- The signature of `n` in the term index (`TermIndex::add`): its operator
applied to the representatives of its arguments, without the empty ones of a
concatenation; and those representatives. -/
def signature (n : Node) : EEM (Node × Array Node) := do
  let .app op cs := n | return (n, #[])
  let isConcat := n.getKind == .STRING_CONCAT
  let mut c : Array Node := #[]
  for a in cs do
    let r ← rep a
    if isConcat && r == emptyWord then continue
    c := c.push r
  return (.app op c, c)

/-- `checkInit`: the term index, the congruent terms, the string classes, and
the classes equal to a constant. -/
def checkInit : EEM Unit := do
  modifyChk fun c => { c with baseInfo := {}, termIndex := {}, concatChildren := {}, stringLikeEqc := #[] }
  let rlv := (← chk).relevant
  let mut i := 0
  repeat
    let some (j, eqc) ← nextClass i | break
    i := j + 1
    if eqc.typeHint == some .regExp then continue
    let isString := isStringLike eqc
    if isString then modifyChk fun c => { c with stringLikeEqc := c.stringLikeEqc.push eqc }
    let mut var : Option Node := none
    let mut prevConstLike : Bool := false
    for n in ← classTerms eqc do
      -- the constant-like terms (constants: `str.unit` comes with sequences)
      if n.isConst then
        if !prevConstLike || n.isConst then
          setBaseInfo eqc { bestContent := some n, bestScore := 0, base := some n, exp := none }
        prevConstLike := true
      if eqc.typeHint == some .integer then continue
      if ← isCongruent n then continue
      match n with
      | .app _ cs =>
        if cs.isEmpty then continue
        let k := n.getKind
        if k == .EQUAL then continue
        let (sig, c) ← signature n
        match (← chk).termIndex.get? ⟨sig⟩ with
        | some nc =>
          if nc == n then continue
          if k == .STRING_CONCAT && !(← areEq nc n) then
            -- `STRINGS_I_NORM`: equal modulo empty components
            let mut exp : Array Node := #[]
            let mut c0 := 0
            let mut c1 := 0
            let mut expRep : Std.HashMap Key Node := {}
            let ncs := nc.getChildren
            let nnc := n.getChildren
            let getRep (m : Std.HashMap Key Node) (x : Node) : Node := Id.run do
              let mut x := x
              for _ in [0:m.size + 1] do
                match m.get? ⟨x⟩ with
                | some y => x := y
                | none => break
              return x
            while c0 < ncs.size || c1 < nnc.size do
              for t in [0, 1] do
                let nn := if t == 0 then ncs else nnc
                let mut ct := if t == 0 then c0 else c1
                while ct < nn.size do
                  let x := nn[ct]!
                  if x == emptyWord || (← areEq x emptyWord) then
                    if x != emptyWord then exp := exp.push (Node.eqNode x emptyWord)
                    ct := ct + 1
                  else break
                if t == 0 then c0 := ct else c1 := ct
              if c0 < ncs.size then
                if ncs[c0]! != nnc[c1]! then
                  let a := ncs[c0]!
                  let b := nnc[c1]!
                  let ra := getRep expRep a
                  let rb := getRep expRep b
                  if ra != rb then
                    expRep := expRep.insert ⟨rb⟩ ra
                    exp := exp.push (Node.eqNode a b)
                c0 := c0 + 1
                c1 := c1 + 1
            let _ ← sendInference exp (Node.eqNode n nc) "STRINGS_I_NORM"
          -- the relevant one of two congruent terms is indexed
          let mut cong := n
          if rlv.contains ⟨n⟩ && !rlv.contains ⟨nc⟩ then
            modifyChk fun ch => { ch with termIndex := ch.termIndex.insert ⟨sig⟩ n }
            cong := nc
          addCongruent cong
        | none =>
          modifyChk fun ch => { ch with termIndex := ch.termIndex.insert ⟨sig⟩ n }
          if k == .STRING_CONCAT then
            -- the trie of concatenations: each prefix's children
            for l in [0:c.size] do
              let pre := Node.app (.kind .STRING_CONCAT) (c.extract 0 l)
              let ch := ((← chk).concatChildren.get? ⟨pre⟩).getD #[]
              if !ch.contains c[l]! then
                modifyChk fun x => { x with concatChildren := x.concatChildren.insert ⟨pre⟩ (ch.push c[l]!) }
            if c.size == 1 then
              -- `STRINGS_I_NORM_S`: a concatenation of one non-empty component
              if !(← areEq c[0]! n) then
                let mut exp : Array Node := #[]
                let mut ns := n
                for x in cs do
                  if ← areEq x emptyWord then
                    if x != emptyWord then exp := exp.push (Node.eqNode x emptyWord)
                  else ns := x
                let _ ← sendInference exp (Node.eqNode n ns) "STRINGS_I_NORM_S"
              addCongruent n
      | _ =>
        if n.isConst then continue
        -- all variables but the oldest are congruent
        match var with
        | none => var := some n
        | some v =>
          if ← nodeLt n v then
            addCongruent v
            var := some n
          else addCongruent n

/-- `getConstantEqc`. -/
def getConstantEqc (eqc : Node) : EEM (Option Node) := do
  match ← baseInfo? eqc with
  | some { bestContent := some c, .. } => return if c.isConst then some c else none
  | _ => return none

/-- `explainConstantEqc`: the constant of the class of `n`, with its explanation
added to `exp`. -/
def explainConstantEqc (n eqc : Node) (exp : Array Node) : EEM (Option Node × Array Node) := do
  match ← baseInfo? eqc with
  | some bei =>
    let some c := bei.bestContent | return (none, exp)
    if !c.isConst then return (none, exp)
    let exp := match bei.exp with | some e => flattenAnd e exp | none => exp
    let exp := match bei.base with | some b => addToExplanation n b exp | none => exp
    return (some c, exp)
  | none => return (none, exp)

/-- `checkConstantEquivalenceClasses` on the trie of concatenations, below the
prefix `path`, with the constants `vecc` of its components. -/
partial def checkConstEqcIndex (path : Array Node) (vecc : Array (Option Node)) (ensureConst isConst : Bool) :
    EEM Unit := do
  let sig := Node.app (.kind .STRING_CONCAT) path
  if let some n := (← chk).termIndex.get? ⟨sig⟩ then
    let c ← if isConst then pure (some (← mkNConcat (vecc.map (·.getD emptyWord)))) else pure none
    let skip ← match c with
      | some c => areEq n c
      | none => pure false
    if !skip then
      let mut countc := 0
      let mut exp : Array Node := #[]
      let mut vecnc : Array Node := #[]
      let mut contentSize := 0
      for x in n.getChildren do
        if let some emps ← isEqualEmptyWord x then
          exp := addToExplanation x emps exp
          continue
        let some vc := vecc[countc]! | do
          vecnc := vecnc.push x
          continue
        if !isConst then
          vecnc := vecnc.push vc
          contentSize := contentSize + wordLen vc
        if !(← areEq x vc) then
          let nrr ← rep x
          let bei := (← baseInfo? nrr).getD {}
          if let some e := bei.exp then exp := flattenAnd e exp
          exp := addToExplanation x (bei.base.getD x) exp
        else exp := addToExplanation x vc exp
        countc := countc + 1
      if !isConst then
        if contentSize > 0 then
          let nr ← rep n
          let bei := (← baseInfo? nr).getD {}
          let bc := bei.bestContent
          if !(bc.map (·.isConst)).getD false && (bc.isNone || contentSize > bei.bestScore) then
            let nct ← mkNConcat vecnc
            setBaseInfo nr { bestContent := some nct, bestScore := contentSize, base := some n,
                             exp := if exp.isEmpty then bei.exp else some (mkAndU exp) }
            -- `(= x (str.++ "A" x))` is a conflict
            for nctc in nct.getChildren do
              if ← areEq nctc nr then
                let _ ← sendInference exp (Node.notNode (Node.eqNode nctc n)) "STRINGS_I_CYCLE_CONFLICT"
                return
          else setBaseInfo nr bei
      else
        let c := c.getD emptyWord
        if ← hasTerm c then
          let _ ← sendInference exp (Node.eqNode n c) "STRINGS_I_CONST_MERGE"
          return
        else if !(← hasProcessed) then
          let nr ← rep n
          let bei := (← baseInfo? nr).getD {}
          let bcConst := (bei.bestContent.map (·.isConst)).getD false
          if !bcConst then
            setBaseInfo nr { bei with bestContent := some c, base := some n, exp := some (mkAndU exp) }
          else if some c != bei.bestContent then
            exp := match bei.exp with
              | none => addToExplanation n (bei.bestContent.getD c) exp
              | some e => addToExplanation n (bei.base.getD n) (exp.push e)
            let _ ← sendInference exp Node.mkFalse "STRINGS_I_CONST_CONFLICT"
            return
          else setBaseInfo nr bei
  let children ← sortNodes (((← chk).concatChildren.get? ⟨sig⟩).getD #[])
  for p in children do
    match ← getConstantEqc p with
    | some bc => checkConstEqcIndex (path.push p) (vecc.push (some bc)) ensureConst isConst
    | none =>
      if !ensureConst then checkConstEqcIndex (path.push p) (vecc.push none) ensureConst false
    if ← hasProcessed then break

/-- `checkConstantEquivalenceClasses`: to a fixed point, the classes entailed
to be constants; then the classes' best content. -/
def checkConstantEquivalenceClasses : EEM Unit := do
  repeat
    let prev := (← chk).baseInfo.size
    checkConstEqcIndex #[] #[] true true
    if (← hasProcessed) || (← chk).baseInfo.size <= prev then break
  if !(← hasProcessed) then checkConstEqcIndex #[] #[] false true

/-! ## Normal forms (`NormalForm`) -/

namespace NormalForm

/-- `init`. -/
def init (base : Node) : NormalForm :=
  { base, nf := if base.isConst && wordLen base == 0 then #[] else #[base] }

def reverse (nf : NormalForm) : NormalForm := { nf with nf := nf.nf.reverse, isRev := !nf.isRev }

/-- `addToExplanation`. -/
def addExp (nf : NormalForm) (exp : Node) (newVal newRevVal : Nat) : NormalForm :=
  let d := if nf.exp.contains exp then nf.exp else nf.exp.push exp
  let dep := match nf.expDep.get? ⟨exp⟩ with
    | none => (newVal, newRevVal)
    | some (f, r) => (if newVal > f then f else newVal, if newRevVal > r then newRevVal else r)
  { nf with exp := d, expDep := nf.expDep.insert ⟨exp⟩ dep }

/-- `getExplanation`. -/
def getExplanation (nf : NormalForm) (index : Int) (cur : Array Node) : Array Node :=
  if index < 0 then cur ++ nf.exp else
  nf.exp.foldl (fun acc e =>
    let (f, r) := (nf.expDep.get? ⟨e⟩).getD (0, 0)
    let dep := if nf.isRev then r else f
    if (dep : Int) <= index then acc.push e else acc) cur

/-- `getExplanationForPrefixEq`. -/
def explainPrefixEq (nfi nfj : NormalForm) (ii ij : Int) (cur : Array Node) : Array Node :=
  let cur := nfi.getExplanation ii cur
  let cur := nfj.getExplanation ij cur
  cur.push (Node.eqNode nfi.base nfj.base)

/-- `splitConstant`: the component at `index` split into `c1` and `c2`. -/
def splitConst (nf : NormalForm) (index : Nat) (c1 c2 : Node) : NormalForm :=
  let v := nf.nf
  let v := (v.extract 0 (index + 1)).set! index c1 ++ #[c2] ++ v.extract (index + 1) v.size
  let size := v.size
  let dep := nf.expDep.fold (fun m k (f, r) =>
    let inc (b : Bool) (x : Nat) : Nat :=
      let increment := if b == nf.isRev then x > index else (size - 1 - x) < index
      if increment then x + 1 else x
    m.insert k (inc false f, inc true r)) {}
  { nf with nf := v, expDep := dep }

/-- `collectConstantStringAt`: the constants from `index` on, concatenated (in
order), and the index after them. -/
def collectConstantStringAt (nf : NormalForm) (index : Nat) : Option Node × Nat := Id.run do
  let mut c : Array Node := #[]
  let mut i := index
  while i < nf.nf.size && nf.nf[i]!.isConst do
    c := c.push nf.nf[i]!
    i := i + 1
  if c.isEmpty then return (none, i)
  return (some (mkConcatA (if nf.isRev then c.reverse else c)), i)

end NormalForm

/-! ## The core solver (`CoreSolver`) -/

def normalForm (n : Node) : EEM NormalForm := do
  return ((← chk).normalForms.get? ⟨n⟩).getD default

def CoreInferInfo.upd (i : CoreInferInfo) (f : Inference → Inference) : CoreInferInfo :=
  { i with infer := f i.infer }

def pushPinfer (i : CoreInferInfo) : EEM Unit := modifyChk fun c => { c with pinfers := c.pinfers.push i }

/-- `checkCycles` from the class `eqc`: its concatenations' flat forms, and the
classes in an acyclic order; a cycle through `eqc` makes the other components
empty. The class closing a cycle, if any, and the explanation. -/
partial def checkCyclesRec (eqc : Node) (curr exp : Array Node) : EEM (Option Node × Array Node) := do
  if curr.contains eqc then return (some eqc, exp)
  if (← chk).stringsEqc.contains eqc then return (none, exp)
  let curr := curr.push eqc
  let mut exp := exp
  let rlv := (← chk).relevant
  let mut hasRlv := false
  for n in ← classTerms eqc do
    if !rlv.contains ⟨n⟩ then continue
    hasRlv := true
    if n.getKind != .STRING_CONCAT || (← isCongruent n) then continue
    if eqc != emptyWord then
      modifyChk fun c => { c with eqcConcats := c.eqcConcats.insert ⟨eqc⟩ (((c.eqcConcats.get? ⟨eqc⟩).getD #[]).push n) }
    let cs := n.getChildren
    for i in [0:cs.size] do
      let nc := cs[i]!
      let nr ← rep nc
      if eqc == emptyWord then
        if nr != emptyWord then
          let _ ← sendInference #[Node.eqNode n emptyWord] (Node.eqNode nc emptyWord) "STRINGS_I_CYCLE_E"
          return (none, exp)
      else
        if nr != emptyWord then
          modifyChk fun c => { c with
            flatForm := c.flatForm.insert ⟨n⟩ (((c.flatForm.get? ⟨n⟩).getD #[]).push nr)
            flatFormIndex := c.flatFormIndex.insert ⟨n⟩ (((c.flatFormIndex.get? ⟨n⟩).getD #[]).push i) }
        let (ncy, exp') ← checkCyclesRec nr curr exp
        exp := exp'
        if let some ncy := ncy then
          exp := addToExplanation n eqc exp
          exp := addToExplanation nr nc exp
          if ncy == eqc then
            for j in [0:cs.size] do
              if j != i && !(← areEq cs[j]! emptyWord) then
                let _ ← sendInference exp (Node.eqNode cs[j]! emptyWord) "STRINGS_I_CYCLE"
                return (none, exp)
            return (none, exp)
          else return (some ncy, exp)
        else if ← hasProcessed then return (none, exp)
  if hasRlv then modifyChk fun c => { c with stringsEqc := c.stringsEqc.push eqc }
  return (none, exp)

/-- `checkCycles`. -/
def checkCycles : EEM Unit := do
  modifyChk fun c => { c with flatForm := {}, flatFormIndex := {}, eqcConcats := {}, stringsEqc := #[] }
  for r in (← chk).stringLikeEqc do
    let _ ← checkCyclesRec r #[] #[]
    if ← hasProcessed then return

def ff (n : Node) : EEM (Array Node) := return ((← chk).flatForm.get? ⟨n⟩).getD #[]
def ffi (n : Node) : EEM (Array Nat) := return ((← chk).flatFormIndex.get? ⟨n⟩).getD #[]

/-- `checkFlatForm`: the flat forms of the concatenations `eqc` of a class,
from the one at `start`, unified left to right (`isRev`: right to left). -/
def checkFlatForm (eqc : Array Node) (start : Nat) (isRev : Bool) : EEM Unit := do
  let mut count := 0
  let mut inelig : Array Node := eqc.extract 0 (start + 1)
  let mut a := eqc[start]!
  let mut b := a
  let mut lant : Option Node := none
  repeat
    let mut exp : Array Node := #[]
    let mut conc : Option Node := none
    let mut infType := ""
    let asize := (← ff a).size
    if count == asize then
      for i in [start + 1 : eqc.size] do
        b := eqc[i]!
        if inelig.contains b then continue
        let bsize := (← ff b).size
        if count < bsize then
          let fb ← ffi b
          let cc := (List.range (bsize - count)).toArray.map fun j =>
            Node.eqNode b.getChildren[fb[count + j]!]! emptyWord
          conc := some (mkAndU cc)
          infType := "STRINGS_F_ENDPOINT_EMP"
          a := eqc[i]!
          b := eqc[start]!
          break
        inelig := inelig.push eqc[i]!
    else
      let curr := (← ff a)[count]!
      let currC ← getConstantEqc curr
      let ac := a.getChildren[(← ffi a)[count]!]!
      let (lcurr, lexp) ← getLength ac #[]
      for i in [start + 1 : eqc.size] do
        b := eqc[i]!
        if inelig.contains b then continue
        let ffb ← ff b
        if count == ffb.size then
          inelig := inelig.push b
          let fa ← ffi a
          let cc := (List.range (asize - count)).toArray.map fun j =>
            Node.eqNode a.getChildren[fa[count + j]!]! emptyWord
          conc := some (mkAndU cc)
          infType := "STRINGS_F_ENDPOINT_EMP"
          break
        let cc := ffb[count]!
        if cc != curr then
          let bc := b.getChildren[(← ffi b)[count]!]!
          inelig := inelig.push b
          let ccC ← getConstantEqc cc
          if let (some cuc, some ccc) := (currC, ccC) then
            if (splitConstant ccc cuc isRev).isNone then
              let (_, e1) ← explainConstantEqc ac curr exp
              let (_, e2) ← explainConstantEqc bc cc e1
              exp := e2
              conc := some Node.mkFalse
              infType := "STRINGS_F_CONST"
              break
          else if asize - 1 == count && ffb.size - 1 == count then
            conc := some (Node.eqNode ac bc)
            infType := "STRINGS_F_ENDPOINT_EQ"
            break
          else
            let (lcc, lexp2) ← getLength bc #[]
            if ← areEq lcurr lcc then
              let lexpc := addToExplanation lcurr lcc (lexp ++ lexp2)
              lant := some (mkAndU lexpc)
              conc := some (Node.eqNode ac bc)
              infType := "STRINGS_F_UNIFY"
              break
    if let some cn := conc then
      let fa ← ffi a
      let fb ← ffi b
      for j in [0:count] do
        exp := addToExplanation a.getChildren[fa[j]!]! b.getChildren[fb[j]!]! exp
      for t in [0, 1] do
        let c := if t == 0 then a else b
        let nc := c.getNumChildren
        let jj : Int := if infType == "STRINGS_F_ENDPOINT_EQ" || (t == 1 && infType == "STRINGS_F_ENDPOINT_EMP") then
            (if isRev then -1 else nc)
          else (if t == 0 then fa[count]! else fb[count]!)
        let startj : Int := if isRev then jj + 1 else 0
        let endj : Int := if isRev then nc else jj
        let mut j := startj
        while j < endj do
          let x := c.getChildren[j.toNat]!
          if ← areEq x emptyWord then exp := addToExplanation x emptyWord exp
          j := j + 1
      exp := addToExplanation a b exp
      if let some l := lant then exp := exp.push l
      let _ ← sendInference exp cn infType isRev
      return
    count := count + 1
    if inelig.size >= eqc.size then break

/-- `checkFlatForms`. -/
def checkFlatForms : EEM Unit := do
  -- (1) the constant components of the flat forms of a constant class must
  -- occur in it, in order
  for eqc in (← chk).stringsEqc do
    let some c ← getConstantEqc eqc | continue
    for n in ((← chk).eqcConcats.get? ⟨eqc⟩).getD #[] do
      let f ← ff n
      if !canConstantContainList c f then
        let fi ← ffi n
        let firstc := f.findIdx? (·.isConst)
        let lastc := (f.reverse.findIdx? (·.isConst)).map (f.size - 1 - ·)
        let mut exp : Array Node := #[]
        if let (some fc, some lc) := (firstc, lastc) then
          for e in [fc : lc + 1] do
            if f[e]!.isConst then exp := addToExplanation n.getChildren[fi[e]!]! f[e]! exp
        let (_, exp') ← explainConstantEqc n eqc exp
        let _ ← sendInference exp' Node.mkFalse "STRINGS_F_NCTN"
        return
  -- (2) unification of the flat forms
  for eqc in (← chk).stringsEqc do
    let ns := ((← chk).eqcConcats.get? ⟨eqc⟩).getD #[]
    if ns.size <= 1 then continue
    for start in [0 : ns.size - 1] do
      for r in [0, 1] do
        checkFlatForm ns start (r == 1)
        if ← inConflict then return
        for n in ns do
          modifyChk fun c => { c with
            flatForm := c.flatForm.modify ⟨n⟩ (·.reverse)
            flatFormIndex := c.flatFormIndex.modify ⟨n⟩ (·.reverse) }

/-- `getNormalForms`: the normal forms of the relevant terms of the class, and
the index of each term's. -/
def getNormalForms (eqc : Node) : EEM (Array NormalForm × Std.HashMap Key Nat) := do
  let mut eqcNonC := eqc
  let mut nfs : Array NormalForm := #[]
  let mut idx : Std.HashMap Key Nat := {}
  let rlv := (← chk).relevant
  for n in ← classTerms eqc do
    if !(n.isConst || (!(← isCongruent n) && rlv.contains ⟨n⟩)) then continue
    let isCLike := n.isConst
    if !(isCLike || n.getKind == .STRING_CONCAT) then
      eqcNonC := n
      continue
    let mut cur : NormalForm := NormalForm.init n
    if !isCLike then
      cur := { base := n }
      for x in n.getChildren do
        let nr ← rep x
        let nfr ← normalForm nr
        let origSize := cur.nf.size
        let addSize := nfr.nf.size
        cur := { cur with nf := cur.nf ++ nfr.nf }
        for e in nfr.exp do
          let (f, r) := (nfr.expDep.get? ⟨e⟩).getD (0, 0)
          cur := cur.addExp e (origSize + f) (origSize + (addSize - r))
        if nfr.base != x then
          cur := cur.addExp (Node.eqNode x nfr.base) origSize (origSize + addSize)
      let total := cur.nf.size
      cur := { cur with expDep := cur.expDep.fold (fun m k (f, r) => m.insert k (f, total - r)) {} }
    if cur.nf.size > 1 || (cur.nf.size == 1 && cur.nf[0]!.isConst) then
      idx := idx.insert ⟨n⟩ nfs.size
      nfs := nfs.push cur
  if nfs.isEmpty then nfs := #[NormalForm.init eqcNonC]
  return (nfs, idx)

/-- `processLoop`, as far as it goes without regular expressions: the conflict
of constants, and the splits on emptiness; otherwise skipped, and the check is
incomplete. -/
def processLoop (nfi nfj : NormalForm) (loopIndex index : Nat) (info : CoreInferInfo) :
    EEM (Option (Option CoreInferInfo)) := do
  let veci := nfi.nf
  let vecoi := nfj.nf
  let tYz ← mkNConcat (veci.extract index loopIndex)
  let sZy ← mkNConcat (vecoi.extract (index + 1) vecoi.size)
  let r ← mkNConcat (veci.extract (loopIndex + 1) veci.size)
  let mut info := info
  let mut sZy := sZy
  let mut r := r
  if sZy.isConst && r.isConst && r != emptyWord then
    -- `String::tailcmp`
    let x := (word? sZy).getD []
    let y := (word? r).getD []
    let tail : Option Int := Id.run do
      let mut i : Int := x.length - 1
      let mut j : Int := y.length - 1
      while i >= 0 && j >= 0 do
        if x[i.toNat]! != y[j.toNat]! then return none
        i := i - 1
        j := j - 1
      return some (if i == -1 then -(j + 1) else i + 1)
    match tail with
    | some c =>
      if c >= 0 then
        sZy := wordSubstr sZy 0 (some c.toNat)
        r := emptyWord
      else
        let _ ← sendInference info.infer.exp Node.mkFalse "STRINGS_FLOOP_CONFLICT" false true
        return some none
    | none =>
      let _ ← sendInference info.infer.exp Node.mkFalse "STRINGS_FLOOP_CONFLICT" false true
      return some none
  for i in [0, 1] do
    let t := if i == 0 then veci[loopIndex]! else tYz
    let splitEq := Node.eqNode t emptyWord
    let splitEqr ← rw splitEq
    if !splitEqr.isConst then
      match ← explainNonEmpty t with
      | none =>
        info := (info.upd fun ii => { ii with exp := #[], id := "STRINGS_LEN_SPLIT_EMP", conc := Node.mkNode .OR #[splitEq, Node.notNode splitEq] })
        return some (some info)
      | some e => info := (info.upd fun ii => { ii with exp := info.infer.exp.push e })
  -- the conclusion needs regular expressions (stage 3)
  modifyChk fun c => { c with modelUnsound := true }
  return none

/-- `processSimpleNEq`: the normal forms `nfi` and `nfj` of equal terms,
unified from `index` (`isRev`: from the end), up to `rproc` components from
the end; an inference (sent or possible) if they differ. Whether they are the
same, and the normal forms and index after. -/
def processSimpleNEq (nfi nfj : NormalForm) (index : Nat) (isRev : Bool) (rproc : Nat) :
    EEM (Bool × NormalForm × NormalForm × Nat) := do
  let mut nfi := nfi
  let mut nfj := nfj
  let mut index := index
  repeat
    let nfiv := nfi.nf
    let nfjv := nfj.nf
    let lhsDone := index == nfiv.size - rproc
    let rhsDone := index == nfjv.size - rproc
    if lhsDone && rhsDone then return (true, nfi, nfj, index)
    if lhsDone || rhsDone then
      let nfkv := if lhsDone then nfjv else nfiv
      let currExp := NormalForm.explainPrefixEq nfi nfj (-1) (-1) #[]
      let mut k := index
      while !(← inConflict) && k < nfkv.size - rproc do
        let _ ← sendInference currExp (Node.eqNode nfkv[k]! emptyWord) "STRINGS_N_ENDPOINT_EMP" isRev
        k := k + 1
      break
    let x := nfiv[index]!
    let y := nfjv[index]!
    if ← areEq x y then
      index := index + 1
      continue
    let (xLen, lenExp) ← getLength x #[]
    let (yLen, lenExp) ← getLength y lenExp
    if ← areEq xLen yLen then
      let ant := NormalForm.explainPrefixEq nfi nfj index index #[]
      if x.isConst && y.isConst then
        let _ ← sendInference ant Node.mkFalse "STRINGS_N_CONST" isRev true
        return (false, nfi, nfj, index)
      let lenExp := addToExplanation xLen yLen lenExp
      let _ ← sendInference (ant.push (mkAndU lenExp)) (Node.eqNode x y) "STRINGS_N_UNIFY" isRev
      break
    if (!x.isConst && index == nfiv.size - rproc - 1) || (!y.isConst && index == nfjv.size - rproc - 1) then
      let mut eqn : Array Node := #[]
      for v in [nfiv, nfjv] do
        let mut eqnc : Array Node := #[]
        for i in [index : v.size - rproc] do
          eqnc := if isRev then #[v[i]!] ++ eqnc else eqnc.push v[i]!
        eqn := eqn.push (← mkNConcat eqnc)
      if !(← areEq eqn[0]! eqn[1]!) then
        let antec := NormalForm.explainPrefixEq nfi nfj (-1) (-1) #[]
        let _ ← sendInference antec (Node.eqNode eqn[0]! eqn[1]!) "STRINGS_N_ENDPOINT_EQ" isRev true
      else return (true, nfi, nfj, index)
      break
    if x.isConst && y.isConst then
      let xw := (word? x).getD []
      let yw := (word? y).getD []
      let minLen := min xw.length yw.length
      if wordNcmp xw yw minLen isRev then
        let xShorter := xw.length < yw.length
        let cl := if xShorter then y else x
        let ns := if xShorter then x else y
        let clw := (word? cl).getD []
        let rem := if isRev then mkWord (clw.take (clw.length - minLen)) else mkWord (clw.drop minLen)
        if xShorter then nfj := nfj.splitConst index ns rem else nfi := nfi.splitConst index ns rem
        index := index + 1
        continue
      else
        let antec := NormalForm.explainPrefixEq nfi nfj index index #[]
        let _ ← sendInference antec Node.mkFalse "STRINGS_N_CONST" isRev true
        break
    -- a possible inference
    let mut info : CoreInferInfo := { infer := { id := "UNKNOWN", conc := Node.mkTrue }, index, rev := isRev }
    if !(← areDiseq xLen yLen) && !(← areEq xLen yLen) && !x.isConst && !y.isConst then
      let lenEq ← rw (Node.eqNode xLen yLen)
      pushPinfer (info.upd fun ii => { ii with id := "STRINGS_LEN_SPLIT", conc := Node.mkNode .OR #[lenEq, negLit lenEq], phases := #[(lenEq, true)] })
      break
    -- `detectLoop`
    let mut loop : Option (Bool × Nat) := none
    for r in [0, 1] do
      let nfv := if r == 0 then nfiv else nfjv
      let nfov := if r == 0 then nfjv else nfiv
      if nfov[index]!.isConst then continue
      let mut found := false
      for lp in [index + 1 : nfv.size - rproc] do
        if nfv[lp]! == nfov[index]! then
          if r == 0 || loop.isNone then loop := some (r == 0, lp)
          found := true
          break
      if found && r == 0 then break
    if let some (inI, lp) := loop then
      if !isRev then
        let info0 := (info.upd fun ii => { ii with exp := NormalForm.explainPrefixEq nfi nfj (-1) (-1) #[] })
        let res ← if inI then processLoop nfi nfj lp index info0 else processLoop nfj nfi lp index info0
        match res with
        | some (some i) => pushPinfer i; break
        | some none => break
        | none => pure ()
    if x.isConst || y.isConst then
      let xc := x.isConst
      let nfc := if xc then nfi else nfj
      let nfnc := if xc then nfj else nfi
      let nc := nfnc.nf[index]!
      match ← explainNonEmpty nc with
      | none =>
        let eq ← rw (Node.eqNode nc emptyWord)
        if eq.isConst then
          let p := Node.mkPurifySkolem nc
          note (.skolem p)
          let pEq := Node.eqNode p emptyWord
          let conc := Node.mkNode .AND #[Node.eqNode p nc, if eq != Node.mkTrue then Node.notNode pEq else pEq]
          pushPinfer (info.upd fun ii => { ii with id := "STRINGS_INFER_EMP", conc := conc })
        else
          pushPinfer (info.upd fun ii => { ii with id := "STRINGS_LEN_SPLIT_EMP", conc := Node.mkNode .OR #[eq, Node.notNode eq] })
        break
      | some expNonEmpty =>
        let (nextConstStr, ncIndex) := nfnc.collectConstantStringAt (index + 1)
        if let some ncs := nextConstStr then
          let (stra, cIndex) := nfc.collectConstantStringAt index
          let stra ← rw (stra.getD emptyWord)
          let strb ← rw ncs
          let p := sufficientNonEmptyOverlap stra strb isRev
          if p > 1 then
            let ant := NormalForm.explainPrefixEq nfc nfnc cIndex ncIndex #[]
            let xcv := Node.mkNode .STRING_CONCAT (if isRev then #[strb, nc] else #[nc, strb])
            let _ := xcv
            let (conc, sk) ← concatCPropConclusion nc strb stra isRev
            pushPinfer (info.upd fun ii => { ii with id := "STRINGS_SSPLIT_CST_PROP", conc := conc, exp := ant.push expNonEmpty, skolems := #[(sk, .split)], idRev := isRev })
            break
        let (conc, sk) ← concatCSplitConclusion nc nfc.nf[index]! isRev
        let ant := NormalForm.explainPrefixEq nfi nfj index index #[]
        pushPinfer (info.upd fun ii => { ii with id := "STRINGS_SSPLIT_CST", conc := conc, exp := ant.push expNonEmpty, skolems := #[(sk, .split)], idRev := isRev })
        break
    -- two non-constants of different lengths
    let mut lentTest : Option Nat := none
    let mut lenConstraint : Option Node := none
    let mut noExplain : Array Node := #[]
    for e in [0, 1] do
      let (lt1, lt2) := if e == 0 then (xLen, yLen) else (yLen, xLen)
      let entLit ← rw (Node.mkNode .GT #[lt1, lt2])
      -- the arithmetic entailment (`entailmentCheck`), by the rewriter
      if entLit == Node.mkTrue then
        lentTest := some e
        lenConstraint := some entLit
        noExplain := noExplain.push entLit
        break
    let mut lcVec : Array Node := match lenConstraint with
      | none => #[Node.notNode (Node.eqNode xLen yLen)]
      | some l => flattenAnd l #[]
    let ant := NormalForm.explainPrefixEq nfi nfj index index #[]
    for t in [x, y] do
      match ← explainNonEmpty t with
      | some tnz => lcVec := lcVec.push tnz
      | none =>
        let tnz := Node.notNode (Node.eqNode x emptyWord)
        lcVec := lcVec.push tnz
        noExplain := noExplain.push tnz
    let (id, conc, sk) ← match lentTest with
      | none => do
        let (c, k) ← concatSplitConclusion x y isRev false
        pure ("STRINGS_SSPLIT_VAR", c, k)
      | some 0 => do
        let (c, k) ← concatSplitConclusion x y isRev true
        pure ("STRINGS_SSPLIT_VAR_PROP", c, k)
      | some _ => do
        let (c, k) ← concatSplitConclusion y x isRev true
        pure ("STRINGS_SSPLIT_VAR_PROP", c, k)
    let _ := sk
    pushPinfer (info.upd fun ii => { ii with id := id, conc := conc, exp := ant.push (mkAndU lcVec), noExplain := noExplain, idRev := isRev })
    break
  return (false, nfi, nfj, index)

/-- `isNormalFormPair`. -/
def isNormalFormPair (n1 n2 : Node) : EEM Bool := do
  let (n1, n2) := if ← nodeLt n2 n1 then (n2, n1) else (n1, n2)
  return (((← st).nfPairs.get? ⟨n1⟩).getD #[]).contains n2

/-- `addNormalFormPair`. -/
def addNormalFormPair (n1 n2 : Node) : EEM Unit := do
  if ← isNormalFormPair n1 n2 then return
  let (n1, n2) := if ← nodeLt n2 n1 then (n2, n1) else (n1, n2)
  let v := (((← st).nfPairs.get? ⟨n1⟩).getD #[]).push n2
  modifyStrings fun s => s.setNfPairs n1 v

/-- `processNEqc`: the normal forms of a class, unified pairwise. -/
def processNEqc (eqc : Node) (nfs : Array NormalForm) : EEM (Array NormalForm) := do
  if nfs.size <= 1 then return nfs
  let mut nfs := nfs
  let c ← getConstantEqc eqc
  let mut nfCache : Array (Node × Nat) := #[]
  let mut nfIndices : Array Nat := #[]
  let mut hasConstIndex := false
  for i in [0:nfs.size] do
    let nfi := nfs[i]!
    let ni ← mkNConcat nfi.nf
    if nfCache.any (·.1 == ni) then continue
    if let some c := c then
      if !canConstantContainList c nfi.nf then
        let (_, exp) ← explainConstantEqc nfi.base eqc nfi.exp
        let _ ← sendInference exp Node.mkFalse "STRINGS_N_NCTN"
        return nfs
    nfCache := nfCache.push (ni, i)
    if ni.isConst then
      hasConstIndex := true
      nfIndices := #[i] ++ nfIndices
    else nfIndices := nfIndices.push i
  let nnfs := nfIndices.size
  for i in [0 : nnfs - 1] do
    for j in [i + 1 : nnfs] do
      let ii := nfIndices[i]!
      let jj := nfIndices[j]!
      if ← isNormalFormPair nfs[ii]!.base nfs[jj]!.base then continue
      -- the reverse direction first
      let (ret, ri, rj, rindex) ← processSimpleNEq nfs[ii]!.reverse nfs[jj]!.reverse 0 true 0
      nfs := (nfs.set! ii ri.reverse).set! jj rj.reverse
      if ret then break
      if ← hasProcessed then break
      let (ret, fi, fj, _) ← processSimpleNEq nfs[ii]! nfs[jj]! 0 false rindex
      nfs := (nfs.set! ii fi).set! jj fj
      if ret then break
      if ← hasProcessed then break
    if hasConstIndex || (← hasProcessed) then break
  if ← inConflict then return nfs
  -- conflicts of normal forms that rewrite to disequal terms
  for (ni, i) in nfCache do
    for (nj, j) in nfCache do
      if !(← nodeLt ni nj) then continue
      if (← rw (Node.eqNode ni nj)) == Node.mkFalse then
        let exp := nfs[i]!.exp ++ nfs[j]!.exp
        let exp := exp.push (Node.eqNode nfs[i]!.base nfs[j]!.base)
        let _ ← sendInference exp Node.mkFalse "STRINGS_N_EQ_CONF"
        return nfs
    if ← hasProcessed then break
  return nfs

/-- `normalizeEquivalenceClass`. -/
def normalizeEquivalenceClass (eqc : Node) : EEM Unit := do
  if ← areEq eqc emptyWord then
    modifyChk fun c => { c with normalForms := c.normalForms.insert ⟨eqc⟩ (NormalForm.init emptyWord) }
    return
  let (nfs, idx) ← getNormalForms eqc
  if ← hasProcessed then return
  let nfs ← processNEqc eqc nfs
  if (← hasProcessed) || !(← chk).pinfers.isEmpty then return
  let i := (idx.get? ⟨eqc⟩).getD 0
  modifyChk fun c => { c with normalForms := c.normalForms.insert ⟨eqc⟩ nfs[i]! }

/-- `checkNormalFormsEqProp`: the normal forms of the classes; two classes of
the same normal form are equal (`STRINGS_NORMAL_FORM`). -/
def checkNormalFormsEqProp : EEM Unit := do
  modifyChk fun c => { c with pinfers := #[], modelUnsound := false, normalForms := {} }
  let mut nfToEqc : Std.HashMap Key Node := {}
  for eqc in (← chk).stringsEqc do
    normalizeEquivalenceClass eqc
    if ← hasProcessed then return
    if !(← chk).pinfers.isEmpty then return
    let nfe ← normalForm eqc
    let nfTerm ← mkNConcat nfe.nf
    match nfToEqc.get? ⟨nfTerm⟩ with
    | some e =>
      let nfeEq ← normalForm e
      let nfExp := if nfeEq.exp.isEmpty then nfe.exp else nfe.exp.push (mkAndU nfeEq.exp)
      let _ ← sendInference nfExp (Node.eqNode nfe.base nfeEq.base) "STRINGS_NORMAL_FORM"
      if ← hasProcessed then return
    | none => nfToEqc := nfToEqc.insert ⟨nfTerm⟩ eqc

/-- The order of the core solver's inferences (`InferenceId`). -/
def inferRank (id : String) : Nat :=
  match id with
  | "STRINGS_INFER_EMP" => 0
  | "STRINGS_SSPLIT_CST_PROP" => 1
  | "STRINGS_SSPLIT_VAR_PROP" => 2
  | "STRINGS_LEN_SPLIT" => 3
  | "STRINGS_LEN_SPLIT_EMP" => 4
  | "STRINGS_SSPLIT_CST" => 5
  | "STRINGS_SSPLIT_VAR" => 6
  | "STRINGS_FLOOP" => 7
  | _ => 8

/-- `checkNormalFormsEq`: the best possible inference (`pickInferInfo`), as a
lemma. -/
def checkNormalFormsEq : EEM Unit := do
  let ps := (← chk).pinfers
  if !ps.isEmpty then
    let mut use := 0
    for i in [1:ps.size] do
      let a := ps[i]!
      let b := ps[use]!
      if inferRank a.infer.id < inferRank b.infer.id ||
          (inferRank a.infer.id == inferRank b.infer.id && a.index > b.index) then use := i
    sendInferenceInfo ps[use]!.infer true
    return
  if (← chk).modelUnsound then
    modifyStrings fun s => { s with incomplete := true }
    modifyChk fun c => { c with modelUnsound := false }

/-- `processSimpleDeq`: the normal forms of disequal terms of equal length,
from `index`; whether the disequality is satisfied (or an inference made). -/
def processSimpleDeq (nfi nfj : Array Node) (ni nj : Node) (index : Nat) (isRev : Bool) :
    EEM (Bool × Array Node × Array Node × Nat) := do
  let mut nfi := nfi
  let mut nfj := nfj
  let mut index := index
  let nfni ← normalForm ni
  let nfnj ← normalForm nj
  while index < nfi.size || index < nfj.size do
    if index >= nfi.size || index >= nfj.size then
      let (niLen, ant) ← getLengthExp ni #[] nfni.base false
      let (njLen, ant) ← getLengthExp nj ant nfnj.base false
      let ant := (ant.push (Node.eqNode niLen njLen)) ++ nfni.exp ++ nfnj.exp
      let nfk := if index >= nfi.size then nfj else nfi
      let cc := (nfk.extract index nfk.size).map fun x => Node.eqNode x emptyWord
      let _ ← sendInference ant (mkAndN cc) "STRINGS_DEQ_NORM_EMP" isRev true
      return (true, nfi, nfj, index)
    let x := nfi[index]!
    let y := nfj[index]!
    if ← areEq x y then
      index := index + 1
      continue
    if !x.isConst || !y.isConst then
      let (xLen, lenExp) ← getLength x #[]
      let (yLen, _) ← getLength y lenExp
      if (← areEq xLen yLen) && (← areDiseq x y) then return (true, nfi, nfj, index)
      return (false, nfi, nfj, index)
    let xw := (word? x).getD []
    let yw := (word? y).getD []
    let shortLen := min xw.length yw.length
    if !wordNcmp xw yw shortLen isRev then return (true, nfi, nfj, index)
    let nl := if xw.length < yw.length then yw else xw
    let rem := if isRev then mkWord (nl.take (nl.length - shortLen)) else mkWord (nl.drop shortLen)
    if xw.length < yw.length then
      nfj := ((nfj.extract 0 (index + 1)).set! index nfi[index]!) ++ #[rem] ++ nfj.extract (index + 1) nfj.size
    else
      nfi := ((nfi.extract 0 (index + 1)).set! index nfj[index]!) ++ #[rem] ++ nfi.extract (index + 1) nfi.size
    index := index + 1
  return (false, nfi, nfj, index)

/-- `processDeq`: the disequality of the classes `ni` and `nj`, of equal
lengths. -/
def processDeq (ni nj : Node) : EEM Unit := do
  let nfni ← normalForm ni
  let nfnj ← normalForm nj
  -- `str.unit` comes with sequences: a disequality of normal forms of one
  -- component is satisfied
  if nfni.nf.size <= 1 && nfnj.nf.size <= 1 then return
  for (eqcN, other) in [(ni, nfnj.nf), (nj, nfni.nf)] do
    if let some c ← getConstantEqc eqcN then
      if !canConstantContainList c other then return
  -- `processReverseDeq`
  let (ret, _, _, _) ← processSimpleDeq nfni.nf.reverse nfnj.nf.reverse ni nj 0 true
  if ret then return
  let mut nfi := nfni.nf
  let mut nfj := nfnj.nf
  let mut index := 0
  while index < nfi.size || index < nfj.size do
    let (ret, nfi', nfj', index') ← processSimpleDeq nfi nfj ni nj index false
    if ret then return
    nfi := nfi'
    nfj := nfj'
    index := index'
    if index >= nfi.size || index >= nfj.size then return
    let x := nfi[index]!
    let y := nfj[index]!
    if ← areEq x y then
      index := index + 1
      continue
    let (xLen, lenExp) ← getLength x #[]
    let (yLen, _) ← getLength y lenExp
    if ← areDiseq xLen yLen then
      if x.isConst || y.isConst then
        let ck := if x.isConst then x else y
        let nck := if x.isConst then y else x
        let nckLen := if x.isConst then yLen else xLen
        match ← explainNonEmpty nck with
        | none =>
          let _ ← sendSplit nck emptyWord "STRINGS_DEQ_DISL_EMP_SPLIT"
          return
        | some _ =>
          let ckw := (word? ck).getD []
          let firstChar := if ckw.length == 1 then ck else mkWord (ckw.take 1)
          if ← areEq nckLen (intConst 1) then
            if ← areDiseq firstChar nck then return
            else if !(← areEq firstChar nck) then
              if ← sendSplit firstChar nck "STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT" false then return
          else
            let (conc, sk1, sk2) ← decomposeConclusion nck (intConst 1) false
            let antecLen := #[Node.mkNode .GEQ #[nckLen, intConst 1]]
            let _ ← sendInference antecLen conc "STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT" false true antecLen
            let _ := (sk1, sk2)
            return
      else
        for r in [0, 1] do
          let ux := if r == 0 then x else y
          let uy := if r == 0 then y else x
          let uxLen := mkLen ux
          let uyLen := mkLen uy
          let (conc, _, _) ← decomposeConclusion ux uyLen false
          let lenConstraint := Node.mkNode .GEQ #[uxLen, uyLen]
          if (← rw lenConstraint) == Node.mkFalse then continue
          let _ ← sendInference #[lenConstraint] conc "STRINGS_DEQ_DISL_STRINGS_SPLIT" false true #[lenConstraint]
        return
    else if ← areEq xLen yLen then
      if ← sendSplit x y "STRINGS_DEQ_STRINGS_EQ" false then return
    else
      if ← sendSplit xLen yLen "STRINGS_DEQ_LENS_EQ" then return
    -- a split that rewrites to a constant: the next component
    index := index + 1

/-- `checkNormalFormsDeq`: the disequalities of strings, by length, then by
their normal forms. -/
def checkNormalFormsDeq : EEM Unit := do
  let deqs := (← st).disequalities
  let mut processed : Array (Node × Node) := #[]
  let mut rlvDeq : Array Node := #[]
  for eq in deqs do
    let .app (.kind .EQUAL) #[a, b] := eq | continue
    let n0 ← rep a
    let n1 ← rep b
    if processed.contains (n0, n1) then continue
    processed := processed.push (n0, n1)
    let (l0, _) ← getLength n0 #[] false
    let (l1, _) ← getLength n1 #[] false
    if ← areEq l0 l1 then rlvDeq := rlvDeq.push eq
    else if !(← areDiseq l0 l1) then
      let _ ← sendSplit l0 l1 "STRINGS_DEQ_LENGTH_SP"
  modifyChk fun c => { c with rlvDeq }
  if ← hasProcessed then return
  for eq in rlvDeq do
    let .app (.kind .EQUAL) #[a, b] := eq | continue
    processDeq (← rep a) (← rep b)
    if ← hasProcessed then return

/-- `checkLengthsEqc`: the length of a class is that of its normal form
(`STRINGS_LEN_NORM`). -/
def checkLengthsEqc : EEM Unit := do
  for eqc in (← chk).stringsEqc do
    let nfi ← normalForm eqc
    let some ei := (← st).getEqcInfo? eqc | continue
    let some llt := ei.lengthTerm | continue
    if ei.normalizedLength.isSome then continue
    let nf ← mkNConcat nfi.nf
    let .app (.kind .STRING_LENGTH) #[lltArg] := llt | continue
    let ant := nfi.exp.push (Node.eqNode lltArg nfi.base)
    let lc := mkLen nf
    let lcr ← rw lc
    if !(← areEq llt lcr) then
      let eq := Node.eqNode llt lc
      modifyStrings fun s => s.setEqcInfo eqc { ei with normalizedLength := some eq }
      let _ ← sendInference ant eq "STRINGS_LEN_NORM" false true

/-! ## Extended functions (`ExtfSolver`), stage 2 in part

The evaluation of the active extended terms under the current substitution
(`checkExtfEval`): the constants of the classes of their arguments (effort 0)
or their normal forms (effort 1). A term that then rewrites to a constant is
inferred equal to it (`STRINGS_EXTF`, `STRINGS_EXTF_N`), stated of its
symbolic definition (its constants replaced by their proxy variables) when it
has one, and marked inactive; a predicate equal to a constant that rewrites to
another literal infers it (`STRINGS_EXTF_D`); two terms with the same rewrite
are equal (`STRINGS_EXTF_REW_SAME`). The inferences of `str.contains`
(`STRINGS_CTN_*`) and of equalities by the extended rewriter
(`STRINGS_EXTF_EQ_REW`, the identity on integers) belong to the reductions of
stage 2. -/

/-- `CoreSolver::getNormalString`: the concatenation of the normal form of `x`,
its explanation added to `exp`. -/
partial def getNormalString (x : Node) (exp : Array Node) : EEM (Node × Array Node) := do
  if x.isConst then return (x, exp)
  let xr ← rep x
  match (← chk).normalForms.get? ⟨xr⟩ with
  | some nf =>
    let ret ← mkNConcat nf.nf
    return (ret, addToExplanation x nf.base (exp ++ nf.exp))
  | none =>
    if let .app (.kind .STRING_CONCAT) cs := x then
      let mut exp := exp
      let mut vs : Array Node := #[]
      for c in cs do
        let (v, e) ← getNormalString c exp
        exp := e
        vs := vs.push v
      return (← mkNConcat vs, exp)
    return (x, exp)

/-- `BaseSolver::explainBestContentEqc`. -/
def explainBestContentEqc (n eqc : Node) (exp : Array Node) : EEM (Option Node × Array Node) := do
  match ← baseInfo? eqc with
  | some bei =>
    let exp := match bei.exp with | some e => flattenAnd e exp | none => exp
    let exp := match bei.base with | some b => addToExplanation n b exp | none => exp
    return (bei.bestContent, exp)
  | none => return (none, exp)

/-- `ExtfSolver::getCurrentSubstitutionFor` (efforts below 3). -/
def currentSubstitution (effort : Nat) (n : Node) (exp : Array Node) : EEM (Node × Array Node) := do
  let nr ← rep n
  if effort ≥ 1 && isStringLike n then
    let some nf := (← chk).normalForms.get? ⟨nr⟩ | return (n, exp)
    if let .app (.kind .STRING_CONCAT) cs := n then
      if n != nf.base then
        let mut exp := exp
        let mut vec : Array Node := #[]
        for c in cs do
          let cr ← rep c
          let nfc ← normalForm cr
          let (nsc, e) ← getNormalString nfc.base exp
          exp := addToExplanation c nfc.base e
          vec := vec.push nsc
        return (← mkNConcat vec, exp)
    let (ns, exp) ← getNormalString nf.base exp
    return (ns, addToExplanation n nf.base exp)
  let (c, cexp) ← explainBestContentEqc n nr #[]
  let mut c := c
  let mut cexp := cexp
  if c.isSome then
    if let .app (.kind .STRING_CONCAT) cs := n then
      cexp := #[]
      let mut vec : Array Node := #[]
      for nc in cs do
        let ncr ← rep nc
        let (cc, e) ← explainBestContentEqc nc ncr cexp
        cexp := e
        vec := vec.push (cc.getD nc)
      c := some (← mkNConcat vec)
  match c with
  | some cc => return (cc, exp ++ cexp)
  | none => return (n, exp)

/-- `TermRegistry::getSymbolicDefinition`: the term with its leaves replaced by
their proxy variables (the equalities added to `exp`); none if a leaf has none.
The children of a regular expression are kept. -/
partial def symbolicDefinition (n : Node) (exp : Array Node) : EEM (Option Node × Array Node) := do
  let leaf := match n with
    | .app _ cs => cs.isEmpty
    | _ => true
  if leaf then
    let some pn := (← st).proxyVar.get? ⟨n⟩ | return (none, exp)
    let eq ← rw (Node.eqNode n pn)
    return (some pn, if exp.contains eq then exp else exp.push eq)
  let .app op cs := n | return (none, exp)
  let mut exp := exp
  let mut out : Array Node := #[]
  for c in cs do
    if n.typeHint == some .regExp then out := out.push c
    else
      let (s, e) ← symbolicDefinition c exp
      exp := e
      let some s := s | return (none, exp)
      out := out.push s
  return (some (.app op out), exp)

/-- `InferenceManager::sendInternalInference`. -/
partial def sendInternalInference (exp : Array Node) (conc : Node) (id : String) : EEM Bool := do
  match conc with
  | .app (.kind .AND) cs =>
    let mut ret := true
    for c in cs do ret := (← sendInternalInference exp c id) && ret
    return ret
  | .app (.kind .NOT) #[.app (.kind .OR) cs] =>
    let mut ret := true
    for c in cs do ret := (← sendInternalInference exp (negLit c) id) && ret
    return ret
  | _ =>
  let (lit, pol) := match conc with
    | .app (.kind .NOT) #[a] => (a, false)
    | a => (a, true)
  if let .app (.kind .EQUAL) #[a, b] := lit then
    for x in [a, b] do
      if !x.isConst && !(← hasTerm x) then return false
    if ← (if pol then areEq a b else areDiseq a b) then return true
  else if lit.isConst then
    if lit == Node.mkTrue then return true
  else if !(← hasTerm lit) then return false
  else if ← areEq lit (Node.mkBool pol) then return true
  let _ ← sendInference exp conc id
  return true

/-- The information of an extended term in one evaluation (`ExtfInfoTmp`). -/
structure ExtfInfo where
  const : Option Node := none
  exp : Array Node := #[]
  initExp : Array Node := #[]
  deriving Inhabited

/-- `ExtfSolver::checkExtfEval` at effort 0 or 1. -/
def checkExtfEval (effort : Nat) : EEM Unit := do
  let terms := (← st).activeExt
  let mut infos : Std.HashMap Key ExtfInfo := {}
  let mut toOrig : Std.HashMap Key Node := {}
  let mut inferProcessed : Std.HashSet Key := {}
  for n in terms do
    let r ← rep n
    let mut einfo : ExtfInfo := { const := ← getConstantEqc r }
    let .app op cs := n | continue
    let mut exp : Array Node := #[]
    let mut schildren : Array Node := #[]
    let mut schanged := false
    for c in cs do
      let (sc, e) ← currentSubstitution effort c exp
      exp := e
      schildren := schildren.push sc
      schanged := schanged || sc != c
    let mut reduced := false
    let mut toReduce := n
    if schanged then
      let sn := Node.app op schildren
      einfo := { einfo with initExp := einfo.initExp ++ exp, exp := einfo.exp ++ exp }
      let nrc ← rw sn
      if nrc.isConst then
        modifyStrings fun s => s.markInactive n
        -- the symbolic definition, unless it rewrites
        let (nrs, _) ← symbolicDefinition sn #[]
        let nrs : Option Node ← match nrs with
          | some d => do
            let dr ← rw d
            pure (if dr != d then none else some d)
          | none => pure none
        let isBool := n.typeHint == some .boolean
        let mut conc : Option Node := none
        match nrs with
        | some d =>
          if !(← areEq d nrc) then
            conc := some (if isBool then (if nrc == Node.mkTrue then d else Node.notNode d) else Node.eqNode d nrc)
            einfo := { einfo with exp := #[] }
        | none =>
          if !(← areEq n nrc) then
            conc := some (if isBool then (if nrc == Node.mkTrue then n else Node.notNode n) else Node.eqNode n nrc)
        if let some cc := conc then
          let id := if effort == 0 then "STRINGS_EXTF" else "STRINGS_EXTF_N"
          let _ ← sendInference einfo.exp cc id false true
        reduced := true
      else
        if let some c := einfo.const then
          if nrc.typeHint == some .boolean && nrc != n then
            let pol := c == Node.mkTrue
            let nrcAssert := if pol then nrc else Node.notNode nrc
            let nAssert := if pol then n else Node.notNode n
            einfo := { einfo with exp := einfo.exp.push nAssert }
            let id := if effort == 0 then "STRINGS_EXTF_D" else "STRINGS_EXTF_D_N"
            let _ ← sendInternalInference einfo.exp nrcAssert id
        toReduce := nrc
    infos := infos.insert ⟨n⟩ einfo
    if !reduced && !inferProcessed.contains ⟨n⟩ then
      inferProcessed := inferProcessed.insert ⟨n⟩
      -- `checkExtfInference`: a term with the same rewrite before
      match toOrig.get? ⟨toReduce⟩ with
      | some no =>
        if !(← areEq n no) then
          let eito := (infos.get? ⟨no⟩).getD {}
          let _ ← sendInference (einfo.initExp ++ eito.initExp) (Node.eqNode n no) "STRINGS_EXTF_REW_SAME"
      | none => toOrig := toOrig.insert ⟨toReduce⟩ n
    if ← inConflict then return

/-! ## Codes (`CodePointSolver`) -/

/-- `CodePointSolver::checkCodes`: injectivity of `str.to_code` on the
relevant disequal classes (`STRINGS_CODE_INJ`). -/
def checkCodes : EEM Unit := do
  if !(← st).hasStrCode then return
  let negOne := intConst (-1)
  let mut codes : Std.HashMap Key Node := {}
  for eqc in (← chk).stringLikeEqc do
    if eqc.typeHint != some .string then continue
    let codeArg ← if eqc.isConst then do
        if wordLen eqc != 1 then continue
        match (← st).proxyVar.get? ⟨eqc⟩ with
        | some p => pure p
        | none => continue
      else
        match ((← st).getEqcInfo? eqc).bind (·.codeTerm) with
        | some a => pure a
        | none => continue
    let vc := Node.mkNode .STRING_TO_CODE #[codeArg]
    if ← areEq vc negOne then continue
    codes := codes.insert ⟨eqc⟩ vc
  if (← hasProcessed) || codes.size ≤ 1 then return
  for eq in (← chk).rlvDeq do
    let .app (.kind .EQUAL) #[a, b] := eq | continue
    let some c0 := codes.get? ⟨← rep a⟩ | continue
    let some c1 := codes.get? ⟨← rep b⟩ | continue
    if ← areDiseq c0 c1 then continue
    let .app _ #[x0] := c0 | continue
    let .app _ #[x1] := c1 | continue
    let deq := Node.notNode (Node.eqNode c0 c1)
    let inj := Node.mkNode .OR #[Node.eqNode c0 negOne, deq, Node.eqNode x0 x1]
    let deq ← rw deq
    modifyStrings fun s => { s with pendingPhases := s.pendingPhases.push (deq, false) }
    let _ ← sendInference #[] inj "STRINGS_CODE_INJ"

/-! ## Regular expressions (`RegExpSolver`), stage 3 in part

At full effort, with model-based reduction (`stringModelBasedReduction`), as
cvc5: the asserted memberships of each class; inclusion between two of them
(`stringRegexpInclusion`: a conflict `STRINGS_RE_INTER_INCLUDE`, or one marked
inactive); evaluation under normal forms (`STRINGS_RE_NF_CONFLICT`) and the
empty string (`STRINGS_RE_DELTA`, `STRINGS_RE_DELTA_CONF`); the unfolding of
the positive ones (`STRINGS_RE_UNFOLD_POS`). Intersection is off
(`re-inter-mode=none`). The negative ones are unfolded at last call, which is
not ported: a `sat` answer then rests on the model check of the memberships. -/

/-- `RegExpSolver::computeAssertions`: the asserted memberships of each class
(by representative, in node order), in the order of the extended terms. -/
def computeAssertedMemberships : EEM (Array (Node × Array Node)) := do
  let mut m : Std.HashMap Key (Array Node) := {}
  for n in (← st).activeExt (some .STRING_IN_REGEXP) do
    let r ← rep n
    if !r.isConst then continue
    let .app _ #[x, _] := n | continue
    let xr ← rep x
    m := m.insert ⟨xr⟩ ((m.getD ⟨xr⟩ #[]).push (if r == Node.mkTrue then n else Node.notNode n))
  let keys ← sortNodes (m.toArray.map (·.1.node))
  return keys.map fun k => (k, m.getD ⟨k⟩ #[])

def atomOf (l : Node) : Bool × Node :=
  match l with
  | .app (.kind .NOT) #[a] => (false, a)
  | a => (true, a)

/-- `RegExpSolver::checkEqcInclusion`, at full effort. -/
def checkEqcInclusion (mems : Array Node) : EEM Bool := do
  let mut remove : Array Node := #[]
  for m1 in mems do
    let (p1, l1) := atomOf m1
    if remove.contains m1 then continue
    for m2 in mems do
      if m1 == m2 then continue
      let (p2, l2) := atomOf m2
      let .app _ #[x1, r1] := l1 | continue
      let .app _ #[x2, r2] := l2 | continue
      if p1 == p2 then
        let basisUnfolded := (← st).reduced.contains ⟨if !p1 then m1 else m2⟩
        -- (the negative ones are unfolded at last call)
        if !basisUnfolded && p1 then
          if regExpIncludes r1 r2 then
            modifyStrings fun s => s.markInactive l1
            remove := remove.push m1
            break
      else
        let (pos, neg) := if !p1 then (l2, l1) else (l1, l2)
        let .app _ #[xp, rp] := pos | continue
        let .app _ #[xn, rn] := neg | continue
        let _ := (x1, x2, r1, r2)
        if regExpIncludes rn rp then
          let mut vec := #[pos, Node.notNode neg]
          if xp != xn then vec := vec.push (Node.eqNode xp xn)
          let _ ← sendInference vec Node.mkFalse "STRINGS_RE_INTER_INCLUDE" false true
          return false
  return true

/-- `RegExpSolver::getNormalSymRegExp`: the strings of `str.to_re` replaced by
their normal forms, rewritten. -/
partial def normalSymRegExp (r : Node) (exp : Array Node) : EEM (Node × Array Node) := do
  match r with
  | .app (.kind .STRING_TO_REGEXP) #[s] =>
    if s.isConst then return (r, exp)
    let (t, exp) ← getNormalString s exp
    return (if t != s then Node.mkNode .STRING_TO_REGEXP #[t] else r, exp)
  | .app (.kind k) cs =>
    if k == .REGEXP_CONCAT || k == .REGEXP_UNION || k == .REGEXP_INTER || k == .REGEXP_STAR ||
        k == .REGEXP_COMPLEMENT then
      let mut exp := exp
      let mut out : Array Node := #[]
      for c in cs do
        let (d, e) ← normalSymRegExp c exp
        exp := e
        out := out.push d
      return (← rw (Node.mkNode k out), exp)
    return (r, exp)
  | _ => return (r, exp)

/-- `RegExpSolver::checkPDerivative` (`stringRegexpDeriveConflicts` is off). -/
def checkPDerivative (x r atom : Node) (nfExp : Array Node) : EEM Unit := do
  let emp := emptyWord
  if !(← areEq x emp) then return
  match delta r with
  | (0, some e) =>
    let noExplain := #[atom, Node.eqNode x emp]
    let _ ← sendInference (nfExp ++ noExplain) e "STRINGS_RE_DELTA" false false noExplain
    modifyStrings fun s => s.markInactive atom
  | (1, _) => modifyStrings fun s => s.markInactive atom
  | (2, _) =>
    let noExplain := if x != emp then #[atom, Node.eqNode x emp] else #[atom]
    let _ ← sendInference (nfExp ++ noExplain) Node.mkFalse "STRINGS_RE_DELTA_CONF" false false noExplain
  | _ => pure ()

/-- `RegExpSolver::checkEvaluations`. -/
def checkEvaluations (mems : Array (Node × Array Node)) : EEM Unit := do
  for (_, as) in mems do
    for assertion in as do
      let (pol, atom) := atomOf assertion
      let .app _ #[x, r] := atom | continue
      let mut nfexp : Array Node := #[]
      let mut r := r
      let mut rnfexp : Array Node := #[]
      let mut nx := x
      if !x.isConst then
        let (t, e) ← getNormalString x nfexp
        nx := t
        nfexp := e
      if !checkConstRegExp r then
        let (r', e) ← normalSymRegExp r rnfexp
        r := r'
        rnfexp := e
        nfexp := nfexp ++ rnfexp
        let tmp ← rw (Node.mkNode .STRING_IN_REGEXP #[nx, r])
        if tmp.isConst then
          if (tmp == Node.mkTrue) == pol then
            modifyStrings fun s => s.markInactive atom
            continue
          else
            let _ ← sendInference (nfexp.push assertion) Node.mkFalse "STRINGS_RE_NF_CONFLICT" false false
              #[assertion]
            break
        if !checkConstRegExp r then continue
      if pol then checkPDerivative x r atom rnfexp

/-- `RegExpSolver::checkUnfold` at full effort: the positive memberships, in
node order, unfolded once (`RegExpOpr::simplify`); one that does not unfold
makes the check incomplete. -/
def checkUnfold (mems : Array (Node × Array Node)) : EEM Unit := do
  let all ← sortNodes (mems.foldl (fun acc (_, as) => acc ++ as) #[])
  for assertion in all do
    let (pol, atom) := atomOf assertion
    if !pol then
      -- (unfolded at last call by cvc5, which telos does not port)
      modifyStrings fun s => { s with negMemUnchecked := true }
      continue
    if (← st).reduced.contains ⟨assertion⟩ then continue
    match reduceRegExpPos atom with
    | some conc =>
      let _ ← sendInference #[assertion] conc "STRINGS_RE_UNFOLD_POS" false false #[assertion]
      modifyStrings fun s => { s with reduced := s.reduced.insert ⟨assertion⟩ }
    | none => modifyStrings fun s => { s with incomplete := true }
  let _ := ()

/-- `RegExpSolver::checkMemberships` at full effort. -/
def checkMemberships : EEM Unit := do
  let mems ← computeAssertedMemberships
  -- `checkInclusions` (intersection is off)
  let mut mems' : Array (Node × Array Node) := #[]
  for (r, as) in mems do
    if !(← checkEqcInclusion as) then return
    mems' := mems'.push (r, as)
  if ← inConflict then return
  checkEvaluations mems
  if ← inConflict then return
  checkUnfold mems

/-- The kinds of the extended functions and regular expressions, which later
stages handle. -/
def laterKind (k : Kind) : Bool :=
  k == .STRING_SUBSTR || k == .STRING_UPDATE || k == .STRING_ITOS || k == .STRING_STOI ||
    k == .STRING_INDEXOF || k == .STRING_INDEXOF_RE || k == .STRING_REPLACE ||
    k == .STRING_REPLACE_ALL || k == .STRING_REPLACE_RE || k == .STRING_REPLACE_RE_ALL ||
    k == .STRING_TO_LOWER || k == .STRING_TO_UPPER || k == .STRING_REV || k == .STRING_CONTAINS ||
    k == .STRING_LEQ || k == .STRING_LT ||
    k == .STRING_FROM_CODE || k == .STRING_IS_DIGIT || k == .STRING_PREFIX || k == .STRING_SUFFIX

/-- `runStrategy` at full effort: the steps, until one has something to process.
-/
def runStrategy : EEM Unit := do
  let steps : List (EEM Unit) := [checkInit, checkConstantEquivalenceClasses, checkExtfEval 0,
    checkCycles, checkFlatForms, checkNormalFormsEqProp, checkNormalFormsEq, checkExtfEval 1,
    checkNormalFormsDeq, checkCodes, checkLengthsEqc, checkMemberships]
  for s in steps do
    s
    if ← hasProcessed then return

/-! ## Processing the pending inferences, in the theory engine's monad -/

section
variable {m : Type → Type} [Monad m] (ops : Ops m)

/-- `assertInternalFact`: the terms of an equality registered, then the fact
asserted to the engine with the conjunction of its premises as its reason,
unless it holds, and the pending conflict (`notifyFact`). -/
def assertInternalFact (ii : Inference) : m Unit := do
  let exp := ii.exp.foldl (fun a p => flattenAnd p a) #[]
  let lit := ii.conc
  let (atom, pol) := match lit with
    | .app (.kind .NOT) #[a] => (a, false)
    | _ => (lit, true)
  let expn := mkAndN exp
  ops.run (note (.fact stringsTheory ii.id lit expn))
  if let .app (.kind .EQUAL) #[a, b] := atom then
    registerTerm ops a
    registerTerm ops b
  ops.run do
    if let .app (.kind .EQUAL) #[a, b] := atom then
      if !pol && isStringLike a then
        modifyStrings fun s => { s with disequalities := s.disequalities.push (Node.eqNode a b) }
    modifyStrings fun s => { s with sentFacts := s.sentFacts + 1, facts := s.facts.insert ⟨lit⟩ (ii.id, expn) }
    let holds ← match atom with
      | .app (.kind .EQUAL) #[a, b] =>
        if !(← hasTerm a) || !(← hasTerm b) then pure false
        else if pol then areEqual a b else areDisequal a b false
      | _ => do
        if !(← hasTerm atom) then pure false
        else areEqual atom (Node.mkBool pol)
    if !holds then
      match atom with
      | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol expn
      | _ => let _ ← assertPredicate atom pol expn
    processPendingConflict

/-- `doPendingFacts`. -/
def doPendingFacts : m Unit := do
  let mut i := 0
  repeat
    let s ← ops.run st
    if (← ops.run inConflict) || i >= s.pendingFacts.size then break
    assertInternalFact ops s.pendingFacts[i]!
    i := i + 1
  ops.run (modifyStrings fun s => { s with pendingFacts := #[] })

/-- `processLemma` and `trustedLemma`: the premises explained (but those of
`noExplain`), the skolems registered, the phases pending, then the lemma
sent. -/
def processLemma (ii : Inference) : m Unit := do
  if let some (a, b) := ii.nfPair then ops.run (addNormalFormPair a b)
  let exp := ii.exp.foldl (fun a p => flattenAnd p a) #[]
  let noExplain := ii.noExplain.foldl (fun a p => flattenAnd p a) #[]
  let assumps ← ops.run (explainPremises exp noExplain)
  let lem :=
    if assumps.isEmpty then ii.conc
    else if ii.conc == Node.mkFalse then negLit (mkAndN assumps)
    else Node.mkNode .IMPLIES #[mkAndN assumps, ii.conc]
  for (k, s) in ii.skolems do registerTermAtomic ops k s
  for (p, b) in ii.phases do
    let p ← ops.run (rw p)
    ops.run (modifyStrings fun s => { s with pendingPhases := s.pendingPhases.push (p, b) })
  let _ ← ops.run (trustedLemma lem ii.id)

/-- `doPendingLemmas`. -/
def doPendingLemmas : m Unit := do
  let mut i := 0
  repeat
    let s ← ops.run st
    if i >= s.pendingLemmas.size then break
    processLemma ops s.pendingLemmas[i]!
    i := i + 1
  ops.run (modifyStrings fun s => { s with pendingLemmas := #[] })

/-- `doPendingPhaseRequirements`: in node order (a `std::map`). -/
def doPendingPhases : m Unit := do
  let ps ← ops.run do
    let ps := (← st).pendingPhases
    modifyStrings fun s => { s with pendingPhases := #[] }
    let mut out : Array (Node × Bool) := #[]
    for p in ps do
      out := match out.findIdx? (·.1 == p.1) with
        | some i => out.set! i p
        | none => out.push p
    let keys ← sortNodes (out.map (·.1))
    return keys.filterMap fun k => out.find? (·.1 == k)
  for (p, b) in ps do ops.phase p b

/-- `doPending`. -/
def doPending : m Unit := do
  doPendingFacts ops
  if ← ops.run inConflict then
    ops.run (modifyStrings fun s => { s with pendingLemmas := #[], pendingPhases := #[] })
    return
  doPendingLemmas ops
  doPendingPhases ops

/-- `TheoryStrings::postCheck`: the pending facts, then, at full effort, the
strategy, repeated while it had something pending and sent no lemma.
`relevant` is the relevant term set; `needCheck` the theory engine's
`Valuation::needCheck`. -/
def postCheck (full : Bool) (relevant : Std.HashSet Key) (needCheck : m Bool) : m Unit := do
  doPendingFacts ops
  if !full || (← ops.run inConflict) || (← needCheck) then return
  ops.run (modifyStrings fun s => { s with incomplete := false, negMemUnchecked := false, chk := { relevant } })
  -- a relevant term of a later stage: the check is incomplete
  if relevant.toArray.any (fun k => laterKind k.node.getKind) then
    ops.run (modifyStrings fun s => { s with incomplete := true })
  repeat
    ops.run (modifyStrings fun s => { s with sentFacts := 0, sentLemmas := 0 })
    ops.run runStrategy
    let hadPending ← ops.run hasPending
    doPending ops
    let sentLemma := (← ops.run st).sentLemmas > 0
    if (← ops.run inConflict) || sentLemma || !hadPending then break

end

end Telos.Solver.Strings
