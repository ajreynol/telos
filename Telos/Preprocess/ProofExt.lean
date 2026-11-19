import Std.Data.HashMap
import Telos.Preprocess.CircuitPropagator

/-!
# CPC proofs of the preprocessor's semantic and substitution steps

The preprocessor's fast steps are justified by Lean theorems, not by CPC proofs
(`Certified.semantic`, `Certified.tri`), so that preprocessing never builds or
checks a proof. For proof output (`telos --post-asserts --proof`), each is
turned into a CPC proof here, from the data its side condition checked, so the
proof follows the step exactly:

* `SemProc.reorg` (the same conjuncts, up to nesting, `true` and repetition):
  under the assumption of each side, its conjuncts by `and_elim`, the other
  side by `and_intro`, then `scope`, and the equivalence (`reorgE`, as
  `andReorg` does);
* `SemProc.learn` (literals learned by Boolean propagation): under the
  assumption of the conjunction, each item of the propagator's trace gets a
  fact from those of the items it depends on, with the clausal rules of the
  propagator's own proofs (`CircuitPropagator.lean`), then the conjunction with
  the learned literals; or, for a conflict, `false` (`learnE`);
* `Certified.tri` (substitutions): under the assumption of the result, each
  justification is a fact (`refl`, `trans` with an entry, `cong`), each chain
  relates a conjunct to its result, and the input follows; under the
  assumption of the input, the conjuncts of the result are derived from the
  last one down, each using the entries of the later ones (`triE`).

Terms are kept as nodes (`PArg.node`), so the proof is linear in the size of
the terms as DAGs. None of this is trusted: the proof is checked by Ethos, or
by Logos with `--check-proof`.
-/

namespace Telos.Preprocess

open Eo Node Proof

/-! ## Reorganizing conjunctions -/

/-- The facts of `n` (at `p`) and, for a conjunction, of its conjuncts, nested
conjunctions split too. -/
partial def splitFacts (n : Node) (p : Nat) (acc : Std.HashMap Key Nat) :
    EmitM (Std.HashMap Key Nat) := do
  if acc.contains ⟨n⟩ then return acc
  let acc := acc.insert ⟨n⟩ p
  match n with
  | .app (.kind .AND) cs =>
    let mut acc := acc
    for h : i in [0:cs.size] do
      if acc.contains ⟨cs[i]⟩ then continue
      let q ← stepE .and_elim [.Numeral (Int.ofNat i)] [p]
      acc ← splitFacts cs[i] q acc
    return acc
  | _ => return acc

/-- The fact `b`, from the facts `F` of conjuncts: one of them, `true`, or a
conjunction of such (`and_intro`). -/
partial def buildConj (F : Std.HashMap Key Nat) (b : Node) : EmitM Nat := do
  if let some p := F.get? ⟨b⟩ then return p
  if b == mkTrue then return ← trueE
  match b with
  | .app (.kind .AND) cs => stepE .and_intro [] (← cs.toList.mapM (buildConj F))
  | _ => throw "reorg: a conjunct of one side is not one of the other"

/-- `(=> a b)`: assume `a`, its conjuncts, `b`, `scope`. -/
def reorgImp (a b : Node) : EmitM Nat := do
  let pa ← assumeE a
  let F ← splitFacts a pa {}
  scopeE (← buildConj F b)

/-- `(= a b)` for a `SemProc.reorg` step. -/
def reorgE (a b : Node) : EmitM Nat := do
  let i₁ ← reorgImp a b
  let i₂ ← reorgImp b a
  equivOfN a b i₁ i₂

/-! ## Learned literals -/

/-- The value of `n`: a Boolean constant's, or the one given so far. -/
def valOf (n : Node) : CPM (Option Bool) := do
  match n with
  | .const (.boolean b) => return some b
  | _ => return (← valueOf n).map (·.1)

/-- The fact of `c` with value `v`, from that of its parent `P` with value `pv`
(at `pp`): `propagateBackward`'s rules. -/
def bwdFact (P : Node) (pv : Bool) (pp : Nat) (c : Node) (v : Bool) : CPM (Option Nat) := do
  let cs := P.getChildren
  let idx := Term.Numeral (Int.ofNat (cs.toList.idxOf c))
  match P.getKind with
  | .AND => if pv then some <$> CPM.lift (stepE .and_elim [idx] [pp]) else andHoldout P pp c
  | .OR => if pv then orHoldout P pp c else some <$> CPM.lift (stepE .not_or_elim [idx] [pp])
  | .NOT => if pv then return some pp else some <$> CPM.lift (stepE .not_not_elim [] [pp])
  | .ITE =>
    let #[cn, t, e] := cs | return none
    match ← valOf cn with
    | some true =>
      if c == t then byClause (if pv then .ite_elim1 else .not_ite_elim1) pp [(cn, true)] else return none
    | some false =>
      if c == e then byClause (if pv then .ite_elim2 else .not_ite_elim2) pp [(cn, false)] else return none
    | none =>
      if c != cn then return none
      if v then byClause (if pv then .ite_elim2 else .not_ite_elim2) pp [(e, !pv)]
      else byClause (if pv then .ite_elim1 else .not_ite_elim1) pp [(t, !pv)]
  | .EQUAL =>
    let #[x, y] := cs | return none
    if c == y then
      if let some vx ← valOf x then return ← eqOther pp pv x vx true
    if c == x then
      if let some vy ← valOf y then return ← eqOther pp pv y vy false
    return none
  | .IMPLIES =>
    let #[x, y] := cs | return none
    -- by the child's value, which tells the sides apart when they are equal
    if pv then
      if v && c == y then byClause .implies_elim pp [(x, true)]
      else if !v && c == x then byClause .implies_elim pp [(y, false)]
      else return none
    else
      if v && c == x then some <$> CPM.lift (stepE .not_implies_elim1 [] [pp])
      else if !v && c == y then some <$> CPM.lift (stepE .not_implies_elim2 [] [pp])
      else return none
  | .XOR =>
    let #[x, y] := cs | return none
    if c == y then
      if let some vx ← valOf x then return ← xorSide pp pv x vx true
    if c == x then
      if let some vy ← valOf y then return ← xorSide pp pv y vy false
    return none
  | _ => return none

/-- The fact of the connective `P` with value `v`, from those of its children:
`propagateForward`'s rules. -/
def fwdFact (P : Node) (v : Bool) : CPM (Option Nat) := do
  let cs := P.getChildren
  let firstWith (w : Bool) : CPM (Option Nat) := do
    for h : i in [0:cs.size] do
      if (← valOf cs[i]) == some w then return some i
    return none
  match P.getKind with
  | .AND =>
    if v then
      let ps ← cs.toList.mapM factPos
      if ps.any Option.isNone then return none
      some <$> CPM.lift (andIntroE (ps.filterMap id))
    else
      let some i ← firstWith false | return none
      byAxiom .cnf_and_pos P (some i) [(cs[i]!, false)]
  | .OR =>
    if v then
      let some i ← firstWith true | return none
      byAxiom .cnf_or_neg P (some i) [(cs[i]!, true)]
    else byAxiom .cnf_or_pos P none (cs.toList.map (·, false))
  | .NOT =>
    let #[c] := cs | return none
    if v then factPos c
    else
      -- `(not (not c))` from `c`, by rewriting it to `c`
      let some q ← factPos c | return none
      let r := rewriteCert (notNode P)
      if r.1 != c then return none
      some <$> CPM.lift (eqResolveE q (← symmOpt (← rwFact r)))
  | .ITE =>
    let #[cn, t, e] := cs | return none
    match ← valOf cn with
    | some true =>
      let some vt ← valOf t | return none
      byAxiom (if vt then .cnf_ite_neg1 else .cnf_ite_pos1) P none [(cn, true), (t, vt)]
    | some false =>
      let some ve ← valOf e | return none
      byAxiom (if ve then .cnf_ite_neg2 else .cnf_ite_pos2) P none [(cn, false), (e, ve)]
    | none => return none
  | .EQUAL =>
    let #[x, y] := cs | return none
    let (some vx, some vy) := (← valOf x, ← valOf y) | return none
    let rule := match vx, vy with
      | true, true => CRule.cnf_equiv_neg2
      | false, false => .cnf_equiv_neg1
      | true, false => .cnf_equiv_pos1
      | false, true => .cnf_equiv_pos2
    byAxiom rule P none [(x, vx), (y, vy)]
  | .IMPLIES =>
    let #[x, y] := cs | return none
    let (some vx, some vy) := (← valOf x, ← valOf y) | return none
    if !vx then byAxiom .cnf_implies_neg1 P none [(x, false)]
    else if vy then byAxiom .cnf_implies_neg2 P none [(y, true)]
    else byAxiom .cnf_implies_pos P none [(x, true), (y, false)]
  | .XOR =>
    let #[x, y] := cs | return none
    let (some vx, some vy) := (← valOf x, ← valOf y) | return none
    let rule := match vx, vy with
      | true, false => CRule.cnf_xor_neg1
      | false, true => .cnf_xor_neg2
      | false, false => .cnf_xor_pos1
      | true, true => .cnf_xor_pos2
    byAxiom rule P none [(x, vx), (y, vy)]
  | _ => return none

/-- The facts of the trace items, in order, under the assumption whose
conjuncts' facts are `conjs`. -/
def traceFacts (L : LearnPlan) (conjs : Array Nat) : CPM (Array Nat) := do
  let mut facts : Array Nat := #[]
  for h : idx in [0:L.trace.size] do
    let it := L.trace[idx]
    let p? ← match it.reason with
      | .root pos => pure conjs[pos]?
      | .bwd par =>
        match L.trace[par]?, facts[par]? with
        | some P, some pp => bwdFact P.node P.value pp it.node it.value
        | _, _ => pure none
      | .fwd _ => fwdFact it.node it.value
    let some p := p? | CPM.lift (throw s!"learn: no fact for trace item {idx}")
    -- the last item of a conflict keeps the earlier value of its node
    if (← valueOf it.node).isNone then
      modify fun s => { s with assign := s.assign.insert ⟨it.node⟩ (it.value, p) }
    facts := facts.push p
  return facts

/-- `(= n m)` for a `SemProc.learn` step. -/
def learnE (L : LearnPlan) (n m : Node) : EmitM Nat := do
  let .app (.kind .AND) cs := n | throw "learn: not a conjunction"
  let pa ← assumeE n
  let mut conjs := #[]
  for i in [0:cs.size] do
    conjs := conjs.push (← stepE .and_elim [.Numeral (Int.ofNat i)] [pa])
  let (facts, st) ← (traceFacts L conjs).run {}
  if m == mkFalse then
    -- the last item contradicts the value its node had
    let some it := L.trace.back? | throw "learn: empty trace"
    let p := facts.back!
    let f ← match it.node with
      | .const (.boolean true) =>
        -- the fact `(not true)`
        eqResolveE p (← rwFact (rewriteCert (notNode mkTrue)))
      | .const (.boolean false) => pure p
      | node =>
        match st.assign.get? ⟨node⟩ with
        | some (_, q) => stepE .contra [] (if it.value then [p, q] else [q, p])
        | none => throw "learn: no conflict"
    return ← falseOfE (← scopeE f)
  let lits ← L.lits.toList.mapM fun t => match facts[t]? with
    | some p => pure p
    | none => throw "learn: no fact for a learned literal"
  let i₁ ← scopeE (← andIntroE (conjs.toList ++ lits))
  let pm ← assumeE m
  let mut es := #[]
  for i in [0:cs.size] do
    es := es.push (← stepE .and_elim [.Numeral (Int.ofNat i)] [pm])
  let i₂ ← scopeE (← andIntroE es.toList)
  equivOfN n m i₁ i₂

/-! ## Substitutions -/

structure TriState where
  justs : Std.HashMap Nat Nat := {}
  ents : Std.HashMap Nat Nat := {}
  /-- The facts of the conjuncts of the result, as far as they are known. -/
  conj : Array (Option Nat)

abbrev TriEM := StateT TriState EmitM

/-- The fact `(= lhs rhs)` of entry `E`, from the fact of its conjunct `d`. -/
def entryFact (E : Entry) (d : Node) (pd : Nat) : EmitM Nat :=
  if d == eqNode E.lhs E.rhs then pure pd
  else if d == eqNode E.rhs E.lhs then stepE .symm [] [pd]
  else if E.lhs == d && E.rhs == mkTrue then stepE .true_intro [] [pd]
  else if d == notNode E.lhs && E.rhs == mkFalse then stepE .false_intro [] [pd]
  else throw "tri: an entry is not its conjunct"

/-- The fact of entry `e` (memoized). -/
def entryE (P : TriPlan) (k : Node) (e : Nat) : TriEM Nat := do
  if let some p := (← get).ents.get? e then return p
  let some E := P.entries[e]? | throw "tri: no entry"
  let some (some pd) := (← get).conj[E.pos]? | throw "tri: an entry's conjunct is not derived yet"
  let some d := k.getChildren[E.pos]? | throw "tri: no conjunct"
  let p ← (entryFact E d pd : EmitM Nat)
  modify fun s => { s with ents := s.ents.insert e p }
  return p

/-- The fact `(= a b)` of justification `j` (memoized). -/
partial def justE (P : TriPlan) (k : Node) (j : Nat) : TriEM Nat := do
  if let some p := (← get).justs.get? j then return p
  let some J := P.justs[j]? | throw "tri: no justification"
  let p ← match J.kind with
    | .refl => (stepN .refl [.node J.a] [] : EmitM Nat)
    | .entry e k' =>
      let ef ← entryE P k e
      match P.justs[k']? with
      | some K => if K.a == K.b then pure ef else do
          let kf ← justE P k k'
          (stepE .trans [] [ef, kf] : EmitM Nat)
      | none => throw "tri: no justification"
    | .congr ks =>
      let .app op _ := J.a | throw "tri: congruence of an atom"
      let eqs ← ks.toList.mapM (justE P k)
      (congStep J.a op eqs : EmitM Nat)
    | .body k' =>
      let .app op _ := J.a | throw "tri: body of an atom"
      let e ← justE P k k'
      (congStep J.a op [e] : EmitM Nat)
  modify fun s => { s with justs := s.justs.insert j p }
  return p

/-- The fact `(= c d)` of the chain of conjunct `i`, from `c`. -/
def chainE (P : TriPlan) (k : Node) (rwFacts : Array Nat) (i : Nat) (c : Node) : TriEM Nat := do
  let some steps := P.chains[i]? | throw "tri: no chain"
  let ps ← steps.toList.mapM fun
    | .subst j => justE P k j
    | .rw r => match rwFacts[r]? with
      | some p => pure p
      | none => throw "tri: no rewrite"
  (closeChain c ps.toArray : EmitM Nat)

/-- `(= n k)` for a `Certified.tri` step. -/
def triE (P : TriPlan) (n k : Node) (rwFacts : Array Nat) : EmitM Nat := do
  let .app (.kind .AND) cs := n | throw "tri: not a conjunction"
  let .app (.kind .AND) ds := k | throw "tri: not a conjunction"
  -- `(=> k n)`: every entry holds, each conjunct follows from its result
  let pk ← assumeE k
  let mut dF := #[]
  for i in [0:ds.size] do
    dF := dF.push (some (← stepE .and_elim [.Numeral (Int.ofNat i)] [pk]))
  let run₁ : TriEM (List Nat) := (List.range cs.size).mapM fun i => do
    let eq ← chainE P k rwFacts i cs[i]!
    let some (some di) := (← get).conj[i]? | throw "tri: no conjunct"
    let back ← (stepE .symm [] [eq] : EmitM Nat)
    (stepE .eq_resolve [] [di, back] : EmitM Nat)
  let (ps, _) ← run₁.run { conj := dF }
  let i₁ ← scopeE (← andIntroE ps)
  -- `(=> n k)`: the conjuncts of the result from the last one down
  let pn ← assumeE n
  let mut cF := #[]
  for i in [0:cs.size] do
    cF := cF.push (← stepE .and_elim [.Numeral (Int.ofNat i)] [pn])
  let run₂ : TriEM Unit := do
    for i in (List.range cs.size).reverse do
      let eq ← chainE P k rwFacts i cs[i]!
      let di ← (stepE .eq_resolve [] [cF[i]!, eq] : EmitM Nat)
      modify fun s => { s with conj := s.conj.set! i (some di) }
  let ((), st) ← run₂.run { conj := Array.replicate ds.size none }
  let ds' ← st.conj.toList.mapM fun
    | some p => pure p
    | none => throw "tri: a conjunct is not derived"
  let i₂ ← scopeE (← andIntroE ds')
  equivOfN n k i₂ i₁

/-- The preprocessor's proofs of its semantic and substitution steps. -/
def preprocessExt : Ext where
  semantic p n k := match p with
    | .reorg => reorgE n k
    | .learn L => learnE L n k
  tri P n k facts := triE P n k facts

end Telos.Preprocess
