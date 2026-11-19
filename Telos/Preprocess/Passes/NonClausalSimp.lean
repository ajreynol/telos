import Telos.Preprocess.Pipeline
import Telos.Preprocess.Options
import Telos.Preprocess.CircuitPropagator
import Telos.Preprocess.CircuitPure
import Telos.Preprocess.TriBuild
import Telos.Rewriter.Theory.Arith
import Telos.Rewriter.Theory.Sets
import Telos.Rewriter.Theory.BVNorm

/-!
# The `non-clausal-simp` pass

cvc5's `NonClausalSimp` (`src/preprocessing/passes/non_clausal_simp.cpp`):

1. the circuit propagator learns literals from the assertions
   (`Telos/Preprocess/CircuitPropagator.lean`); a conflict makes the pipeline
   `false` (with the definitions of earlier runs: a conflict in this pass, as in
   cvc5, drops the substitutions it found);
2. each learned literal, simplified by the substitutions found so far
   (`processLearnedLit`), is `true` (dropped), `false` (a conflict), solved by
   its theory into a substitution `x := t` (`TheoryEngine::solve`, the theories'
   `ppAssert`), a constant propagation `t := c` if it equates a term to a
   constant (cvc5's `isConst`, with set constants in normal form), or kept;
3. the substitutions, then the constant propagations (to a fixed point), are
   applied to every assertion, which is rewritten;
4. the kept literals and the constant propagations `(= t c)`, simplified, are
   added after the assertions (unless already there), and the substitutions
   become definitions (the pipeline's definitions slot), with their right-hand
   sides as solved (with proofs, cvc5 adds the proven equations to its top-level
   substitutions).

Ported `ppAssert`: the default one (an equality with a variable side, not in
the other side, of the same type), the Booleans' (a variable, its negation),
and arithmetic's (an equality normalized by `normalizeEquality`, solved for its
head when it is a variable with coefficient 1 and the other side has at most
`ppAssertMaxSubSize = 2` terms; `(= (to_real x) c)` for an integer variable
`x` and an integral `c` is `x := c`), and bit-vectors' (the default one, then
`BvPpAssert`: an extract of a variable equal to a constant, `bvExtractSolve`).
Not ported: arithmetic's other mixed integer and real cases.

The pass is a few certified steps of the conjunction, checked in time linear
in the size of the terms as DAGs (`ncsSteps`): the learned literals added
(`SemProc.learn`, justified by the propagator's trace, `CircuitPure.lean`), and
the substitutions applied (`Certified.tri`, twice, with reorganizations
between, `SemProc.reorg`); a conflict of the propagator is one step to `false`
(`SemProc.learn`, justified by the trace ending with the assignment that found
it). Where those cannot be built (a definition that is not ground, or a
substitution below an application of a term that is not a declared function,
constructor or selector), it is one CPC proof
(`ncsProof`, `Telos/Preprocess/ConjProof.lean`): assuming the conjunction, the
propagator's facts, the substitutions' equations, each assertion's
simplification (congruence with the equations at the leaves, then rewriting)
and the new conjunction; assuming the new conjunction, the old one, from the
definitions; and resolution. If that cannot be proven either, the pass does
nothing. Both give the same conjunction.
-/

namespace Telos.Preprocess

open Eo Node Proof

/-- The fuel of substitution (term depth and fixed point). -/
def substFuel : Nat := 100000

/-- `TheoryEngine::isLegalElimination`: `x` is a variable not in `t`, of the same
type (models are not produced, so any term is allowed). -/
def isLegalElimination (x t : Node) : Bool :=
  x.isVar && !(t.vars.contains x) && x.typeHint.isSome && x.typeHint == t.typeHint

/-- A solved literal: the variable, its value, and the derivation of the fact
`(= x t)` from the fact of the literal. -/
abbrev Solved := Node × Node × (Nat → EmitM Nat)

/-- `Theory::ppAssert`: an equality with a variable side. -/
def defaultPpAssert (l : Node) : Option Solved :=
  match l with
  | .app (.kind .EQUAL) #[a, b] =>
    if isLegalElimination a b then some (a, b, pure)
    else if isLegalElimination b a then some (b, a, fun p => stepE .symm [] [p])
    else none
  | _ => none

/-- `(= x (not t))` from the fact `(not (= x t))` (or `(not (= t x))`, `flip`)
at `p`: `not_equiv_elim1` gives `(or x t)` and `not_equiv_elim2`
`(or (not x) (not t))`, so `(=> x (not t))` and `(=> (not t) x)` under
`scope`, and the equality by resolution (`equivOfE`). -/
def negEqSolve (x t : Node) (p : Nat) : EmitM Nat := do
  let c₁ ← stepE .not_equiv_elim1 [] [p]
  let c₂ ← stepE .not_equiv_elim2 [] [p]
  let pa ← assumeE x
  let r₁ ← stepE .resolution [.Boolean false, x.toEo] [c₂, pa]
  let i₁ ← scopeE r₁
  let pn ← assumeE (notNode t)
  let r₂ ← stepE .resolution [.Boolean true, t.toEo] [c₁, pn]
  let i₂ ← scopeE r₂
  equivOfE x.toEo (notNode t).toEo i₁ i₂

/-- `TheoryBool::ppAssert`. -/
def boolPpAssert (l : Node) : Option Solved :=
  match l with
  | .app (.kind .NOT) #[.app (.kind .EQUAL) #[a, b]] =>
    if a.typeHint != some .boolean then none
    else if isLegalElimination a b then some (a, notNode b, negEqSolve a b)
    else if isLegalElimination b a then some (b, notNode a, negEqSolve b a)
    else none
  | .app (.kind .NOT) #[x] =>
    if x.isVar then some (x, mkFalse, fun p => stepE .false_intro [] [p]) else none
  | x =>
    if x.isVar then some (x, mkTrue, fun p => stepE .true_intro [] [p])
    else defaultPpAssert l

/-- `TheoryArithPrivate::ppAssert`: the equality normalized, solved for its head
if it is a variable (coefficient 1), the other side with at most 2 terms. -/
def arithPpAssert (l : Node) : Option Solved := do
  if l.getKind != .EQUAL then none
  let r : Rw l := (Arith.normalizeEquality l).getD (Rw.id l)
  -- `(= (to_real x) c)` for an integer variable `x` and an integral constant
  -- `c`: solved as `x := c` (cvc5 strips the cast, then makes `c` an integer),
  -- `(= x c)` by `arith_poly_norm_rel`
  let r : Rw l := match r.1 with
    | .app (.kind .EQUAL) #[.app (.kind .TO_REAL) #[v], .const (.rational q)] =>
      if v.isVar && q.isInt then
        let c : Node := .const (.integer q.num)
        (r.next? fun m => Arith.polyNormRel m 1 1 (mkNode .SUB m.getChildren)
          (Arith.toReal (mkNode .SUB #[v, c])) (eqNode v c)).getD r
      else r
    | _ => r
  let #[x, t] := r.1.getChildren | none
  if r.1.getKind != .EQUAL then none
  let size := if t.getKind == .ADD then t.getNumChildren else 1
  if size > 2 then none
  if !isLegalElimination x t then none
  return (x, t, fun p => do eqResolveE p (← rwFact r))

/-- Whether `v` occurs in `n`, with skolems atomic (cvc5's `hasSubterm`),
visiting each shared subterm once. -/
partial def occursAtomic (v n : Node) : Bool :=
  (go n |>.run {}).1
where
  go (m : Node) : StateM (Std.HashSet Node) Bool := do
    if m == v then return true
    if (← get).contains m then return false
    modify (·.insert m)
    match m with
    | .skolem .. => return false
    | _ => m.getChildren.anyM go

/-- `BvPpAssert::ppAssert`: `(= ((_ extract h l) x) c)`, for a variable `x` and
a constant `c`, is `x := (concat sk₁ c sk₂)`, where `sk₁` and `sk₂` purify the
extracts of `x` above `h` and below `l` (either missing at an end). The equation
by `bv-eq-extract-elim1` (`2` for `l = 0`, `3` for `h` the top bit), after
`eq-symm` if the constant is on the left, then `skolem_intro` on the extracts.
As in cvc5, `x` may occur in the skolems (they are atomic). -/
def bvExtractSolve (l : Node) : Option (Node × Node × Rw l) := do
  let .app (.kind .EQUAL) #[a, b] := l | none
  let isExt (n : Node) : Bool := n.getKind == .BITVECTOR_EXTRACT
  let (r₀, e, c) ← if isExt a && b.isConst then some (Rw.id l, a, b)
    else if isExt b && a.isConst then (byRule "eq-symm" l).map (·, b, a)
    else none
  let .app (.indexed .BITVECTOR_EXTRACT #[h, lo]) #[x] := e | none
  if !x.isVar then none
  let w ← BvNorm.width? x
  let rule ← if lo == 0 then (if h + 1 < w then some "bv-eq-extract-elim2" else none)
    else if h + 1 == w then some "bv-eq-extract-elim3" else some "bv-eq-extract-elim1"
  let _ := c
  let r₁ ← r₀.next? (byRule rule)
  let isExtOfX (c : Node) : Bool :=
    match c with
    | .app (.indexed .BITVECTOR_EXTRACT _) #[y] => y == x
    | _ => false
  let purify (c : Node) : Rw c :=
    if isExtOfX c then (purifyStep c).getD (Rw.id c) else Rw.id c
  let r₂ ← r₁.next? fun m => Rw.congrArg m 1 fun cc => some (rewriteChildren (m := Id) purify cc)
  let #[x', t] := r₂.1.getChildren | none
  if x' != x || occursAtomic x t || t.typeHint != x.typeHint then none
  return (x, t, r₂)

/-- `TheoryBV::ppAssert`: the default one, then `BvPpAssert`. -/
def bvPpAssert (l : Node) : Option Solved :=
  (defaultPpAssert l).orElse fun _ =>
    (bvExtractSolve l).map fun (x, t, r) => (x, t, fun p => do eqResolveE p (← rwFact r))

/-- `TheoryEngine::solve`: the `ppAssert` of the theory of the literal's atom. -/
def solveLit (termBased : Bool) (l : Node) : Option Solved :=
  let atom := match l with
    | .app (.kind .NOT) #[a] => a
    | a => a
  match ppTheoryOf termBased atom with
  | .THEORY_BOOL => boolPpAssert l
  | .THEORY_ARITH => arithPpAssert l
  | .THEORY_BV => bvPpAssert l
  | _ => defaultPpAssert l

/-- Substitution facts from an array of `(term, fact, value)`. -/
def factsOf (es : Array (Node × Nat × Node)) : SubstFacts :=
  let m : Std.HashMap Key (Nat × Node) := es.foldl (fun m (t, p, v) => m.insert ⟨t⟩ (p, v)) {}
  fun n => m.get? ⟨n⟩

/-- `applyTrusted(n, rw)` of a substitution: its application to `n`, then the
rewrite, with the fact `(= n result)`; unchanged when the result is `n`. -/
def applyRwE (σ : SubstFacts) (n : Node) : EmitM (Node × Option Nat) := do
  let (n₁, e₁) ← substFact σ substFuel n
  if e₁.isNone then return (n, none)
  let r := rewriteCert n₁
  if r.1 == n then return (n, none)
  return (r.1, ← transOpt e₁ (← rwFact r))

/-- `processLearnedLit` (and the simplification of an assertion): the
substitutions, then the constant propagations to a fixed point, each followed by
the rewriter; the result and the fact `(= n result)`. -/
def simplifyE (σn σc : SubstFacts) (n : Node) : EmitM (Node × Option Nat) := do
  let (n₁, e₁) ← applyRwE σn n
  let mut cur := n₁
  let mut e := e₁
  for _ in [0:1000] do
    let (n₂, e₂) ← applyRwE σc cur
    if e₂.isNone then break
    e ← transOpt e e₂
    cur := n₂
  return (cur, e)

/-- The constant propagation `t := c` of a literal `(= t c)` or `(= c t)`, with
the derivation of `(= t c)`. -/
def constProp? (l : Node) : Option (Node × Node × (Nat → EmitM Nat)) :=
  match l with
  | .app (.kind .EQUAL) #[a, b] =>
    -- cvc5's `isConst`, with set constants in normal form (unions of singletons)
    let isC (n : Node) : Bool := n.isConst || SetsRewriter.isConstNode n
    if isC a && !isC b then some (b, a, fun p => stepE .symm [] [p])
    else if isC b && !isC a then some (a, b, pure)
    else none
  | _ => none

/-- The conflict: `(= C false)` from the fact `false` at `p` under the
assumption `C`. -/
def conflictE (p : Nat) : EmitM Nat := do falseOfE (← scopeE p)

/-- The proof of `(= C C')`, where `C` is the pipeline's conjunction (with the
definitions slot `true`); its last fact, and the literals given to `solveLit`
(`TheoryEngine::solve`, whose arithmetic `ppAssert` records bounds for static
learning). -/
def ncsProof (termBased : Bool) (C : Node) : EmitM (Nat × Array Node) := do
  let .app (.kind .AND) cs := C | throw "not a conjunction"
  -- Forward: assume C.
  let pC ← assumeE C
  let conj ← conjunctsE pC C
  let asserts := conj.dropLast
  -- 1. the circuit propagator
  let ((), cp) ← (do
      for (a, p) in asserts do assertTrue a p
      propagate).run {}
  if let some pFalse := cp.conflict then return (← conflictE pFalse, #[])
  -- 2. the learned literals
  let mut nss : Array (Node × Nat × Node) := #[]
  let mut cps : Array (Node × Nat × Node) := #[]
  let mut kept : Array (Node × Nat) := #[]
  let mut solvedLits : Array Node := #[]
  for (l, pl) in cp.learned do
    let (l', e) ← simplifyE (factsOf nss) (factsOf cps) l
    let pl' ← eqResolveE pl e
    if l' == mkTrue then continue
    if l' == mkFalse then return (← conflictE pl', solvedLits)
    solvedLits := solvedLits.push l'
    match solveLit termBased l' with
    | some (x, t, der) => nss := nss.push (x, ← der pl', t)
    | none =>
      match constProp? l' with
      | some (t, c, der) => cps := cps.push (t, ← der pl', c)
      | none => kept := kept.push (l, pl)
  let σn := factsOf nss
  let σc := factsOf cps
  -- 3. the assertions
  let mut newA : Array (Node × Nat) := #[]
  let mut seen : Std.HashSet Key := {}
  for (a, p) in asserts do
    let (a', e) ← simplifyE σn σc a
    newA := newA.push (a', ← eqResolveE p e)
    seen := seen.insert ⟨a'⟩
  -- 4. the learned literals and constant propagations to conjoin
  let mut extra : Array (Node × Nat) := #[]
  for (l, pl) in kept do
    let (l', e) ← simplifyE σn σc l
    if seen.contains ⟨l'⟩ then continue
    seen := seen.insert ⟨l'⟩
    extra := extra.push (l', ← eqResolveE pl e)
  for (t, pc, c) in cps do
    let (l', e) ← simplifyE σn (fun _ => none) (eqNode t c)
    if seen.contains ⟨l'⟩ then continue
    seen := seen.insert ⟨l'⟩
    extra := extra.push (l', ← eqResolveE pc e)
  -- the definitions, as solved: with proofs, cvc5 adds the proven equations
  -- to its top-level substitutions (`TrustSubstitutionMap::addSubstitutions`),
  -- so their right-hand sides are not substituted
  let finals : Array (Node × Nat × Node) := nss
  let defNodes := finals.toList.map fun (x, _, t) => eqNode x t
  let slotNode := match defNodes with
    | [] => mkTrue
    | [d] => d
    | ds => mkNode .AND ds.toArray
  let pSlot ← if finals.isEmpty then trueE else andIntroE (finals.toList.map (·.2.1))
  let parts := newA.toList ++ extra.toList ++ [(slotNode, pSlot)]
  let C' := mkNode .AND (parts.map (·.1)).toArray
  let i₁ ← scopeE (← andIntroE (parts.map (·.2)))
  -- Backward: assume C'.
  let pC' ← assumeE C'
  let conj' ← conjunctsE pC' C'
  let byNode : Std.HashMap Key Nat := conj'.foldl (fun m (n, p) => m.insert ⟨n⟩ p) {}
  let slotPos := (conj'.getLast?.map (·.2)).getD pC'
  let defFacts ← if finals.isEmpty then pure [] else conjunctsE slotPos slotNode
  let σF := factsOf ((defFacts.zip finals.toList).map fun ((_, p), (x, _, t)) => (x, p, t)).toArray
  -- the constant propagations, from their conjuncts
  let mut cpsB : Array (Node × Nat × Node) := #[]
  for (t, _, c) in cps do
    let (l', e) ← simplifyE σF (fun _ => none) (eqNode t c)
    let some p := byNode.get? ⟨l'⟩ | throw "constant propagation not found"
    cpsB := cpsB.push (t, ← eqResolveE p (← symmOpt e), c)
  let σcB := factsOf cpsB
  -- the old conjuncts
  let mut olds : Array Nat := #[]
  for h : i in [0:asserts.length] do
    let (a, _) := asserts[i]
    let (a', e) ← simplifyE σF σcB a
    let some (b, p) := conj'[i]? | throw "missing conjunct"
    if b != a' then throw "assertion mismatch"
    olds := olds.push (← eqResolveE p (← symmOpt e))
  olds := olds.push (← trueE)
  let i₂ ← scopeE (← andIntroE olds.toList)
  return (← equivOfE C.toEo C'.toEo i₁ i₂, solvedLits)

/-! ## Without a CPC proof

The same pass as `ncsProof`, as semantic and triangular steps, each checked in
time linear in the size of the terms as DAGs:

1. `SemProc.learn`: the learned literals are added after the conjuncts, last
   learned first (`Telos/Core/Learn.lean`), justified by the propagator's trace
   (`runCircuitPure`); or, if the propagator finds a conflict, the conjunction
   becomes `false`.
2. `Certified.tri`: each learned literal is simplified by the substitutions of
   the literals learned before it, which come after it, and solved into its
   equation `(= x t)` or kept as a constant propagation; the assertions are
   simplified by all of them. A kept literal is left as it is.
3. `SemProc.reorg`: the kept literals, then the constant propagations, then the
   equations, in the order they were learned.
4. `Certified.tri`: the kept literals and the constant propagations are
   simplified by the substitutions.
5. `SemProc.reorg`: the conjunction of `ncsProof`, with the definitions slot.

The definitions keep their right-hand sides as solved: with proofs, cvc5 adds
the proven equations of a run to its top-level substitutions as they are
(`TrustSubstitutionMap::addSubstitutions`; without proofs it copies the
substitution map, whose right-hand sides `apply` has substituted). A later run
(`repeat-simp`) finds the definitions of the earlier ones in the slot, and keeps
them before the new ones.

If a step cannot be built, or its check fails, the pass falls back to
`ncsProof`, or, in a later run, does nothing. -/

/-- The equation `(= x t)` of a solved literal `l`, by a certified rewrite. -/
def solvedEq (l x t : Node) : Option (Rw l) :=
  let goal := eqNode x t
  let r : Option (Rw l) :=
    if l == goal then some (Rw.id l)
    else if l == eqNode t x then byRuleWithPremises .eq_symm [t, x] [] l
    else if l == x && t == mkTrue then byRuleWithPremises .symm [] [stepCmd .bool_eq_true [x]] l
    else if l == notNode x && t == mkFalse then
      byRuleWithPremises .symm [] [stepCmd .bool_eq_false [x]] l
    else
      let neg? : Option (Node × Node) := match l with
        | .app (.kind .NOT) #[.app (.kind .EQUAL) #[a, b]] => some (a, b)
        | _ => none
      match neg? with
      | some (a, b) =>
        if a == x && t == notNode b then byRuleWithPremises .bool_not_eq_elim2 [a, b] [] l
        else if b == x && t == notNode a then do
          let r₁ ← byRuleWithPremises .bool_not_eq_elim1 [a, b] [] l
          let r₂ ← byRuleWithPremises .eq_symm [notNode a, b] [] r₁.1
          some (r₁.trans r₂)
        else none
      | none => (Arith.normalizeEquality l).orElse fun _ => (bvExtractSolve l).map (·.2.2)
  r.bind fun r => if r.1 == goal then some r else none

/-- The data of `SemProc.learn` from the propagator's state, for the conjuncts
`cs`: the skeleton (the conjuncts, and the children of connectives, breadth
first), the trace, and the learned literals, last learned first; after a
conflict, the trace ends with the assignment that found it, and there are no
literals. -/
def learnPlanOf (cs : Array Node) (st : CPPState) : Except String LearnPlan := do
  let posOf : Std.HashMap Key Nat := Id.run do
    let mut m : Std.HashMap Key Nat := {}
    for h : i in [0:cs.size] do
      if !m.contains ⟨cs[i]⟩ then m := m.insert ⟨cs[i]⟩ i
    return m
  let (skel, skelOf) := Id.run do
    let mut skel : Array SkelItem := #[]
    let mut skelOf : Std.HashMap Key Nat := {}
    for h : i in [0:cs.size] do
      if !skelOf.contains ⟨cs[i]⟩ then
        skelOf := skelOf.insert ⟨cs[i]⟩ skel.size
        skel := skel.push ⟨cs[i], none, i⟩
    let mut q := 0
    for _ in [0:skel.size + st.trace.size * 64 + 1] do
      if h : q < skel.size then
        let it := skel[q]
        if isBoolConn it.node then
          for (c, j) in it.node.getChildren.toList.zipIdx do
            if !skelOf.contains ⟨c⟩ then
              skelOf := skelOf.insert ⟨c⟩ skel.size
              skel := skel.push ⟨c, some q, j⟩
        q := q + 1
      else break
    return (skel, skelOf)
  -- The propagator asserts the children of conjunctions (`assertTrue`), which
  -- it does not assign: the conjunctions of the conjuncts are first given
  -- `true`, a conjunct as such and a nested one by its parent, and an asserted
  -- node that is not a conjunct is forced by its parent.
  let (syn, parentOf) := Id.run do
    let mut syn : Array LItem := #[]
    let mut idx : Std.HashMap Key Nat := {}
    let mut parentOf : Std.HashMap Key Nat := {}
    let mut stack : Array Nat := #[]
    for h : i in [0:cs.size] do
      if cs[i].getKind == .AND && !idx.contains ⟨cs[i]⟩ then
        idx := idx.insert ⟨cs[i]⟩ syn.size
        stack := stack.push syn.size
        syn := syn.push ⟨cs[i], true, .root i⟩
    for _ in [0:st.trace.size + cs.size + 1] do
      let some j := stack.back? | break
      stack := stack.pop
      for c in syn[j]!.node.getChildren do
        if !parentOf.contains ⟨c⟩ then parentOf := parentOf.insert ⟨c⟩ j
        if c.getKind == .AND && !idx.contains ⟨c⟩ then
          idx := idx.insert ⟨c⟩ syn.size
          stack := stack.push syn.size
          syn := syn.push ⟨c, true, .bwd j⟩
    return (syn, parentOf)
  let off := syn.size
  let trace ← (st.trace ++ st.conflictItem.toArray).mapM fun it => do
    let r ← match it.reason with
      | .root => match posOf.get? ⟨it.node⟩, parentOf.get? ⟨it.node⟩ with
        | some p, _ => pure (LReason.root p)
        | none, some j => pure (LReason.bwd j)
        | none, none => throw "learn: an asserted node is not a conjunct"
      | .fwd => match skelOf.get? ⟨it.node⟩ with
        | some s => pure (LReason.fwd s)
        | none => throw "learn: not in the skeleton"
      | .bwd p => pure (LReason.bwd (p + off))
    pure (⟨it.node, it.value, r⟩ : LItem)
  let lits := if st.conflict then #[] else (st.learned.map (· + off)).reverse
  return { skel, trace := syn ++ trace, lits }

/-- How a learned literal was processed. -/
inductive LitClass where
  | drop
  | conflict
  /-- Kept (the original literal is conjoined, simplified). -/
  | kept
  /-- Solved into `x := t`; the literal became `(= x t)`. -/
  | solved (x t : Node)
  /-- The constant propagation `t := c`; the literal `l'` stays. -/
  | cprop (t c l' : Node)

/-- Run a builder from `B`. -/
def runTri {α : Type} (m : TriM α) (B : TriB) : Except String (α × TriB) := m.run B

/-- The steps of the pass, without a CPC proof (steps 1 to 5 above). -/
def ncsSteps {input : Node} (termBased : Bool) (p : Pipeline input) :
    Except String (Pipeline input × Array Node) := do
  let .app (.kind .AND) cs := p.1 | throw "not a conjunction"
  let asserts := cs.pop
  let nA := asserts.size
  -- 1. the propagator, and the learned literals
  let st := Profile.time "ncs" (fun _ => "propagate") fun _ => runCircuitPure asserts.toList
  let L ← learnPlanOf cs st
  if st.conflict then
    return ← (Profile.time "ncs" (fun _ => "learn (conflict)") fun _ =>
      p.next? fun m => if h : SemProc.check (.learn L) m mkFalse = true then
        some ⟨mkFalse, .semantic (.learn L) (SemProc.check_ok h) (.refl _)⟩ else none).elim
      (throw "conflict: check failed") (fun q => pure (Pipeline.toConflict p q, #[]))
  let K := st.learned.size
  let litOf (h : Nat) : Node := LearnPlan.litOf (L.trace[L.lits[K - 1 - h]!]!)
  let C₁ := mkNode .AND (cs ++ L.lits.map fun t => LearnPlan.litOf L.trace[t]!)
  let some p₁ := Profile.time "ncs" (fun _ => "learn") fun _ =>
      p.next? fun m => if h : SemProc.check (.learn L) m C₁ = true then
        some ⟨C₁, .semantic (.learn L) (SemProc.check_ok h) (.refl _)⟩ else none
    | throw "learn: check failed"
  -- 2. the learned literals, then the assertions
  let litPos (h : Nat) : Nat := nA + 1 + (K - 1 - h)
  let mut B : TriB := {}
  let mut σn : TSubst := {}
  let mut σc : TSubst := {}
  let mut cls : Array LitClass := #[]
  let mut fin₁ : Array (Node × Array ChainStep) := #[]
  let mut conflict := false
  let mut solvedLits : Array Node := #[]
  for h in [0:K] do
    let l := litOf h
    if conflict then
      cls := cls.push .kept; fin₁ := fin₁.push (l, #[]); continue
    let (((l', steps), _, _), B') ← runTri (simplifyJ σn σc {} {} l) B
    B := B'
    if l' == mkTrue then
      cls := cls.push .drop; fin₁ := fin₁.push (l', steps)
    else if l' == mkFalse then
      cls := cls.push .conflict; fin₁ := fin₁.push (l', steps); conflict := true
    else
      solvedLits := solvedLits.push l'
      match solveLit termBased l' with
        | some (x, t, _) =>
          let some r := solvedEq l' x t | throw "solve: no equation"
          let eq := eqNode x t
          let (steps', B') ← runTri (do
              let st ← if r.1 == l' then pure #[] else pure #[← TriM.rw r]
              let e ← TriM.entry x t (litPos h) eq
              pure (steps ++ st, e)) B
          B := B'
          σn := σn.insert ⟨x⟩ steps'.2
          cls := cls.push (.solved x t); fin₁ := fin₁.push (eq, steps'.1)
        | none =>
          match constProp? l' with
          | some (t, c, _) =>
            let (e, B') ← runTri (TriM.entry t c (litPos h) l') B
            B := B'
            σc := σc.insert ⟨t⟩ e
            cls := cls.push (.cprop t c l'); fin₁ := fin₁.push (l', steps)
          | none => cls := cls.push .kept; fin₁ := fin₁.push (l, #[])
  let mut newA : Array (Node × Array ChainStep) := #[]
  if conflict then
    newA := asserts.map fun a => (a, #[])
  else
    let mut cn : SubstCache := {}
    let mut cc : SubstCache := {}
    for a in asserts do
      let ((r, cn', cc'), B') ← runTri (simplifyJ σn σc cn cc a) B
      B := B'; cn := cn'; cc := cc'
      newA := newA.push r
  -- the definitions of an earlier run (`repeat-simp`), as they are
  let slot' := cs.back!
  let slotPart : Node × Array ChainStep := (slot', #[])
  let parts₂ := newA ++ #[slotPart] ++ fin₁.reverse
  let C₂ := mkNode .AND (parts₂.map (·.1))
  let some p₂ := Profile.time "ncs" (fun _ => "tri") fun _ =>
      p₁.next? fun m => triRw m C₂ B (parts₂.map (·.2))
    | throw "tri: check failed"
  if conflict then
    let some p₃ := p₂.next? fun m => checkBy .absorb m mkFalse | throw "conflict"
    return (Pipeline.toConflict p p₃, solvedLits)
  -- 3. reorganized: assertions, kept literals, constant propagations, equations
  let kept := (List.range K).filterMap fun h => match cls[h]? with
    | some LitClass.kept => some (litOf h) | _ => none
  let cprops := cls.toList.filterMap fun | .cprop t c l' => some (t, c, l') | _ => none
  let solved := cls.toList.filterMap fun | .solved x t => some (x, t) | _ => none
  let newAs := newA.map (·.1)
  let C₂' := mkNode .AND (newAs ++ kept.toArray ++ (cprops.map (·.2.2)).toArray ++
    (solved.map fun (x, t) => eqNode x t).toArray ++ #[slot'])
  let some p₃ := p₂.next? fun m =>
      if h : SemProc.reorg.check m C₂' = true then
        some ⟨C₂', .semantic .reorg (SemProc.check_ok h) (.refl _)⟩ else none
    | throw "reorg: check failed"
  -- 4. the equations, from the last; the constant propagations; the kept literals
  let posK := nA
  let posC := posK + kept.length
  let posD := posC + cprops.length
  let mut B₂ : TriB := { rwCache := B.rwCache }
  let mut σD : TSubst := {}
  let mut defs : Array (Node × Node × Array ChainStep) := #[]
  for ((x, t), i) in solved.zipIdx.reverse do
    let (e, B') ← runTri (TriM.entry x t (posD + i) (eqNode x t)) B₂
    B₂ := B'
    σD := σD.insert ⟨x⟩ e
    defs := defs.push (x, t, #[])
  defs := defs.reverse
  let mut cnD : SubstCache := {}
  let mut σcF : TSubst := {}
  let mut cpF : Array (Node × Array ChainStep) := #[]
  for ((t, c, l'), i) in cprops.zipIdx do
    let start := eqNode t c
    let (r, B') ← runTri (do
        let st ← if l' == start then pure #[] else
          match byRuleWithPremises .eq_symm [c, t] [] l' with
          | some r => if r.1 == start then pure #[← TriM.rw r] else throw "cprop: symm"
          | none => throw "cprop: symm"
        let ((e', steps), cn', _) ← simplifyJ σD {} cnD {} start
        let ent ← if e' == start then some <$> TriM.entry t c (posC + i) e' else pure none
        pure (e', st ++ steps, cn', ent)) B₂
    B₂ := B'
    cnD := r.2.2.1
    if let some ent := r.2.2.2 then σcF := σcF.insert ⟨t⟩ ent
    cpF := cpF.push (r.1, r.2.1)
  let mut ccF : SubstCache := {}
  let mut keptF : Array (Node × Array ChainStep) := #[]
  for l in kept do
    let ((r, cn', cc'), B') ← runTri (simplifyJ σD σcF cnD ccF l) B₂
    B₂ := B'; cnD := cn'; ccF := cc'
    keptF := keptF.push r
  let parts₃ := newAs.map (fun a => (a, (#[] : Array ChainStep))) ++ keptF ++ cpF ++
    defs.map (fun (x, t', st) => (eqNode x t', st)) ++ #[(slot', #[])]
  let C₃ := mkNode .AND (parts₃.map (·.1))
  let some p₄ := Profile.time "ncs" (fun _ => "tri (2)") fun _ =>
      p₃.next? fun m => triRw m C₃ B₂ (parts₃.map (·.2))
    | throw "tri (2): check failed"
  -- 5. the conjunction of `ncsProof`
  let mut seen : Std.HashSet Key := newAs.foldl (fun s a => s.insert ⟨a⟩) {}
  let mut extra : Array Node := #[]
  for (l', _) in keptF ++ cpF do
    if seen.contains ⟨l'⟩ then continue
    seen := seen.insert ⟨l'⟩
    extra := extra.push l'
  let oldDefs := match slot' with
    | .app (.kind .AND) ds => ds.toList
    | .const (.boolean true) => []
    | d => [d]
  let defNodes := oldDefs ++ defs.toList.map fun (x, t', _) => eqNode x t'
  let slotNode := match defNodes with
    | [] => mkTrue
    | [d] => d
    | ds => mkNode .AND ds.toArray
  let target := mkNode .AND (newAs ++ extra ++ #[slotNode])
  let some p₅ := p₄.next? fun m =>
      if m == target then some (Rw.id m)
      else if h : SemProc.reorg.check m target = true then
        some ⟨target, .semantic .reorg (SemProc.check_ok h) (.refl _)⟩ else none
    | throw "reorg (2): check failed"
  return (p₅, solvedLits)

/-- The `non-clausal-simp` pass, and the literals given to `solveLit`. -/
def Pipeline.nonClausalSimpB {input : Node} (p : Pipeline input) (termBased : Bool := false) :
    Pipeline input × Array Node :=
  if Pipeline.inConflict p then (p, #[])
  else
    let fast := match ncsSteps termBased p with
      | .ok q => some q
      | .error e => Profile.time "ncs" (fun _ => s!"fallback: {e}") fun _ => none
    match fast with
    | some (q, lits) => (Pipeline.conflictFrom? p q, lits)
    | none =>
      -- `ncsProof` assumes no earlier definitions: a later run is skipped
      if Pipeline.slot p != mkTrue then (p, #[]) else
      match (ncsProof termBased p.1).run {} with
      | .ok ((_, lits), st) =>
        match applyCmds (cmdList (toCmds st.steps)) p.1 with
        | some r => (Pipeline.conflictFrom? p (p.trans r), lits)
        | none => (p, #[])
      | .error _ => (p, #[])

/-- The `non-clausal-simp` pass. -/
def Pipeline.nonClausalSimp {input : Node} (p : Pipeline input) : Pipeline input :=
  (Pipeline.nonClausalSimpB p).1

end Telos.Preprocess
