import Telos.Preprocess.Pipeline
import Telos.Preprocess.CircuitPropagator
import Telos.Rewriter.Theory.Arith

/-!
# The `non-clausal-simp` pass

cvc5's `NonClausalSimp` (`src/preprocessing/passes/non_clausal_simp.cpp`):

1. the circuit propagator learns literals from the assertions
   (`Telos/Preprocess/CircuitPropagator.lean`); a conflict makes the pipeline
   `false`;
2. each learned literal, simplified by the substitutions found so far
   (`processLearnedLit`), is `true` (dropped), `false` (a conflict), solved by
   its theory into a substitution `x := t` (`TheoryEngine::solve`, the theories'
   `ppAssert`), a constant propagation `t := c` if it equates a term to a
   constant, or kept;
3. the substitutions, then the constant propagations (to a fixed point), are
   applied to every assertion, which is rewritten;
4. the kept literals and the constant propagations `(= t c)`, simplified, are
   added after the assertions (unless already there), and the substitutions
   become definitions (the pipeline's definitions slot), with their right-hand
   sides substituted (cvc5 applies its `TopLevelSubstitutions` to a fixed
   point).

Ported `ppAssert`: the default one (an equality with a variable side, not in
the other side, of the same type), the Booleans' (a variable, its negation),
and arithmetic's (an equality normalized by `normalizeEquality`, solved for its
head when it is a variable with coefficient 1 and the other side has at most
`ppAssertMaxSubSize = 2` terms). Not ported: bit-vector extract solving, and arithmetic's
mixed integer and real cases.

The pass is one certified rewrite of the conjunction, by one CPC proof
(`Telos/Preprocess/ConjProof.lean`): assuming the conjunction, the propagator's
facts, the substitutions' equations, each assertion's simplification
(congruence with the equations at the leaves, then rewriting) and the new
conjunction; assuming the new conjunction, the old one, from the definitions;
and resolution. If any step cannot be proven, the pass does nothing.
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
  let #[x, t] := r.1.getChildren | none
  if r.1.getKind != .EQUAL then none
  let size := if t.getKind == .ADD then t.getNumChildren else 1
  if size > 2 then none
  if !isLegalElimination x t then none
  return (x, t, fun p => do eqResolveE p (← rwFact r))

/-- `TheoryEngine::solve`: the `ppAssert` of the theory of the literal's atom. -/
def solveLit (l : Node) : Option Solved :=
  let atom := match l with
    | .app (.kind .NOT) #[a] => a
    | a => a
  match theoryOf atom with
  | .THEORY_BOOL => boolPpAssert l
  | .THEORY_ARITH => arithPpAssert l
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
    if a.isConst && !b.isConst then some (b, a, fun p => stepE .symm [] [p])
    else if b.isConst && !a.isConst then some (a, b, pure)
    else none
  | _ => none

/-- The conflict: `(= C false)` from the fact `false` at `p` under the
assumption `C`. -/
def conflictE (p : Nat) : EmitM Nat := do falseOfE (← scopeE p)

/-- The proof of `(= C C')`, where `C` is the pipeline's conjunction (with the
definitions slot `true`); its last fact. -/
def ncsProof (C : Node) : EmitM Nat := do
  let .app (.kind .AND) cs := C | throw "not a conjunction"
  -- Forward: assume C.
  let pC ← assumeE C
  let conj ← conjunctsE pC C
  let asserts := conj.dropLast
  -- 1. the circuit propagator
  let ((), cp) ← (do
      for (a, p) in asserts do assertTrue a p
      propagate).run {}
  if let some pFalse := cp.conflict then return ← conflictE pFalse
  -- 2. the learned literals
  let mut nss : Array (Node × Nat × Node) := #[]
  let mut cps : Array (Node × Nat × Node) := #[]
  let mut kept : Array (Node × Nat) := #[]
  for (l, pl) in cp.learned do
    let (l', e) ← simplifyE (factsOf nss) (factsOf cps) l
    let pl' ← eqResolveE pl e
    if l' == mkTrue then continue
    if l' == mkFalse then return ← conflictE pl'
    match solveLit l' with
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
  -- the definitions: right-hand sides substituted
  let mut finals : Array (Node × Nat × Node) := #[]
  for (x, pD, t) in nss do
    let (t', e) ← substFact σn substFuel t
    let pF ← match e with
      | none => pure pD
      | some e => do
        let rx ← closeChain x #[]
        let ee ← congStep (eqNode x t) (.kind .EQUAL) [rx, e]
        stepE .eq_resolve [] [pD, ee]
    finals := finals.push (x, pF, t')
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
  equivOfE C.toEo C'.toEo i₁ i₂

/-- The `non-clausal-simp` pass. -/
def Pipeline.nonClausalSimp {input : Node} (p : Pipeline input) : Pipeline input :=
  if Pipeline.inConflict p || Pipeline.slot p != mkTrue then p
  else
    match runE p.1 (ncsProof p.1) with
    | some r => Pipeline.conflict? (p.trans r)
    | none => p

end Telos.Preprocess
