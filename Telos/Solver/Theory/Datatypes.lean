import Telos.Solver.EqualityEngine
import Telos.Solver.Theory.DtType
import Telos.Solver.Theory.UF
import Telos.Rewriter.Rewrite

/-!
# The theory of datatypes

A port of cvc5's `TheoryDatatypes` (`src/theory/datatypes/theory_datatypes.cpp`)
and its inference manager (`inference_manager.cpp`, over
`InferenceManagerBuffered` and `TheoryInferenceManager`), with the central
equality engine, in the configuration of safe mode with proofs:
- no codatatypes (`datatypesExp` is off), so no bisimilarity and no recursive
  singletons; no sygus; no `dt.size` or `dt.height`;
- shared selectors are off (`dtSharedSelectors`, with proofs), splits are not
  binary (`dtBinarySplit`), only one split lemma is sent per check
  (`dtBlastSplits`), cycles are checked (`dtCyclic`), and the instantiation of
  a constructor is a lemma only when it has a finite argument of another type
  (`dtPoliteOptimize`).

The theory reacts to the central equality engine's notifications while it
propagates (`eqNotifyNewClass`, `eqNotifyMerge`), through the engine's hook
(`onNote`): its state is the engine's field `dt`. Its facts, lemmas and
conflicts are recorded as the engine's notes (`Note.fact`, `.lemma`,
`.conflict`), which the theory engine turns into events, in order.

Explanations are as cvc5's proof equality engine computes them: an internal
fact is asserted with its explanation as its reason, so explanations stop at
the explanations of internal facts.
-/

namespace Telos.Solver.DT

open EE

/-! ## The engine and the state -/

def dtTheory : Theory := .THEORY_DATATYPES

/-- `getRepresentative`: the representative of a term, or the term if the
engine does not have it. -/
def rep (n : Node) : EEM Node := do
  let s ← get
  match s.nodeIds.get? ⟨n⟩ with
  | some i => return s.nodes[find s i]!
  | none => return n

def inConflict : EEM Bool := return (← get).teConflict

def st : EEM State := return (← get).dt

def hasEqcInfo (n : Node) : EEM Bool := return (← st).labels.contains ⟨n⟩

/-- The information of a class, if it has some. -/
def eqcInfo? (n : Node) : EEM (Option EqcInfo) := do
  if ← hasEqcInfo n then return some ((← st).getEqcInfo n) else return none

def setInfo (n : Node) (f : EqcInfo → EqcInfo) : EEM Unit :=
  modifyDt fun d => d.setEqcInfo n (f (d.getEqcInfo n))

/-- `getOrMakeEqcInfo` with `doMake`. -/
def makeEqcInfo (n : Node) : EEM EqcInfo := do
  if !(← hasEqcInfo n) then
    modifyDt fun d => d.setLabels n 0
    if (consApp? n).isSome then setInfo n fun e => { e with constructor := some n }
    modifyDt fun d => d.setSelApps n 0
  return (← st).getEqcInfo n

/-- `getEqcConstructor`. -/
def getEqcConstructor (r : Node) : EEM Node := do
  if (consApp? r).isSome then return r
  match ← eqcInfo? r with
  | some { constructor := some c, .. } => return c
  | _ => return r

def numLabels (n : Node) : EEM Nat := return (← st).labels.getD ⟨n⟩ 0
def labelAt (n : Node) (i : Nat) : EEM Label := return ((← st).labelsData.getD ⟨n⟩ #[])[i]!
def numSelApps (n : Node) : EEM Nat := return (← st).selApps.getD ⟨n⟩ 0
def selAppAt (n : Node) (i : Nat) : EEM Node := return ((← st).selAppsData.getD ⟨n⟩ #[])[i]!

def isNot : Node → Bool
  | .app (.kind .NOT) _ => true
  | _ => false

/-- `getLabel`: the positive tester of a class, if it has one. -/
def getLabel (n : Node) : EEM (Option Node) := do
  let k ← numLabels n
  if k > 0 then
    let l ← labelAt n (k - 1)
    if !isNot l.lit then return some l.lit
  return none

/-- `getLabelIndex`. -/
def getLabelIndex (eqc : Option EqcInfo) (n : Node) : EEM (Option Nat) := do
  if let some { constructor := some c, .. } := eqc then
    return (consApp? c).map (·.2.1)
  match ← getLabel n with
  | some l => return (isTester? l).map (·.1)
  | none => return none

/-- `hasLabel`. -/
def hasLabel (eqc : Option EqcInfo) (n : Node) : EEM Bool := do
  if let some { constructor := some _, .. } := eqc then return true
  return (← getLabel n).isSome

/-- `hasTester`. -/
def hasTester (n : Node) : EEM Bool := return (← numLabels n) > 0

/-- `getPossibleCons`. -/
def getPossibleCons (eqc : Option EqcInfo) (n : Node) (T : TypeNode) : EEM (Array Bool) := do
  let li ← getLabelIndex eqc n
  let mut pcons := Array.replicate (numConstructors T) li.isNone
  match li with
  | some l => pcons := pcons.set! l true
  | none =>
    for i in [0:← numLabels n] do
      pcons := pcons.set! (← labelAt n i).index false
  return pcons

/-! ## The inference manager -/

/-- `addPendingInference`: a lemma when forced, or when its conclusion is a
disjunction (`mustCommunicateFact`); an internal fact otherwise. -/
def addPendingInference (conc : Node) (id : String) (exp : Node) (forceLemma : Bool := false) :
    EEM Unit := do
  let i : Inference := { conc, exp, id }
  let isOr := match conc with
    | .app (.kind .OR) _ => true
    | _ => false
  if forceLemma || isOr then modifyDt fun d => { d with pendingLemmas := d.pendingLemmas.push i }
  else modifyDt fun d => { d with pendingFacts := d.pendingFacts.push i }

/-- `notifyInstantiate`: the class of `t` is instantiated. -/
def notifyInstantiate (t : Node) : EEM Unit := do
  let r ← rep t
  let _ ← makeEqcInfo r
  setInfo r fun e => { e with inst := true }

/-- `prepareDtInference`: an instantiation marks its class instantiated when it
is sent. -/
def prepareDtInference (conc : Node) (id : String) : EEM Unit := do
  if id == "DATATYPES_INST" then
    if let .app (.kind .EQUAL) #[a, _] := conc then notifyInstantiate a

/-- `TheoryInferenceManager::trustedLemma`, with the cache of the lemmas sent
(by rewritten lemma). -/
def trustedLemma (lem : Node) (id : String) : EEM Bool := do
  let key : Key := ⟨Telos.rewrite lem⟩
  if (← st).lemmaCache.contains key then return false
  modifyDt fun d => { d with lemmaCache := d.lemmaCache.insert key, sentLemmas := d.sentLemmas + 1,
                             lemmasAdded := true }
  note (.lemma dtTheory id lem)
  return true

/-- `processDtLemma`, then the lemma is sent: `(=> exp conc)`, or `conc` when
there is no explanation. -/
def sendLemma (conc exp : Node) (id : String) : EEM Bool := do
  prepareDtInference conc id
  let lem := if exp == Node.mkTrue then conc else .app (.kind .IMPLIES) #[exp, conc]
  trustedLemma lem id

/-- `sendDtConflict`: the conflict is the explanation of the literals `conf`
(`ProofEqEngine::assertConflict`), unless the engine is already in conflict. -/
def sendDtConflict (conf : Array Node) (id : String) (cycle : Array (Node × Node × Nat) := #[]) :
    EEM Unit := do
  if ← inConflict then return
  modifyDt fun d => { d with conflict := some { id, conf, cycle } }
  let mut assumps : Array Node := #[]
  for e in conf do
    for a in ← explainLit e do
      if !assumps.contains a then assumps := assumps.push a
  note (.conflict dtTheory id (mkAnd assumps))
  modify fun s => { s with teConflict := true }

/-- `reset`. -/
def reset : EEM Unit := modifyDt fun d => { d with sentFacts := 0, sentLemmas := 0 }

def clearPending : EEM Unit := modifyDt fun d => { d with pendingFacts := #[], pendingLemmas := #[] }

/-! ## The theory -/

/-- `getTermSkolemFor`: the purification skolem of a constructor term, with
its defining lemma. -/
def getTermSkolemFor (n : Node) : EEM Node := do
  if (consApp? n).isNone then return n
  match (← st).termSk.get? ⟨n⟩ with
  | some k => return k
  | none =>
    let k := Node.skolem .PURIFY #[n]
    modifyDt fun d => { d with termSk := d.termSk.insert ⟨n⟩ k }
    addPendingInference (Node.eqNode k n) "DATATYPES_PURIFY" Node.mkTrue true
    return k

/-- `getInstantiateCons`. -/
def getInstantiateCons (n : Node) (T : TypeNode) (i : Nat) : EEM Node := do
  if let some (_, _, cs) := consApp? n then
    if cs.isEmpty then return n
  let k ← getTermSkolemFor n
  return getInstCons k T i

/-- `instantiate`: the class of `n` has a label or a constructor; it is equal
to the constructor applied to the selectors of one of its terms. -/
def instantiate (n : Node) : EEM Bool := do
  let eqc ← eqcInfo? n
  let some index ← getLabelIndex eqc n | return false
  let some e := eqc | return false
  if e.inst then return false
  let (exp, tt) ← match e.constructor with
    | some c => pure (Node.mkTrue, c)
    | none => do
      let some lbl ← getLabel n | return false
      let arg := match lbl with
        | .app _ #[a] => a
        | a => a
      pure (lbl, arg)
  let some T := dtType? tt | return false
  let ttCons ← getInstantiateCons tt T index
  if tt == ttCons then
    setInfo n fun e => { e with inst := true }
    return false
  addPendingInference (Node.eqNode tt ttCons) "DATATYPES_INST" exp (hasFiniteExternalArgType T index)
  return true

/-- `collapseSelector`: a selector of the constructor term `c` is the
constructor's argument, unless it is the selector of another constructor. -/
def collapseSelector (s c : Node) : EEM Unit := do
  let some (T, i, j, a) := selApp? s | return
  let some (_, ci, _) := consApp? c | return
  if i != ci then return
  let rrs := Telos.rewrite (mkSel T i j c)
  if s != rrs then
    let forceLemma := (dtType? s).isNone
    addPendingInference (Node.eqNode s rrs) "DATATYPES_COLLAPSE_SEL" (Node.eqNode a c) forceLemma

/-- `addSelector`. -/
def addSelector (s n : Node) (assertFacts : Bool := true) : EEM Unit := do
  let k ← numSelApps n
  let op := match s with
    | .app (.node _ f) _ => some f
    | _ => none
  for j in [0:k] do
    let ss ← selAppAt n j
    let op' := match ss with
      | .app (.node _ f) _ => some f
      | _ => none
    if op == op' then return
  modifyDt fun d => (d.setSelApps n (k + 1)).setSelAppData n k s
  setInfo n fun e => { e with selectors := true }
  if assertFacts then
    if let some c := ((← st).getEqcInfo n).constructor then collapseSelector s c

/-- `addConstructor`. -/
def addConstructor (c n : Node) : EEM Unit := do
  let some (_, ci, _) := consApp? c | return
  for i in [0:← numLabels n] do
    let l ← labelAt n i
    if isNot l.lit && l.index == ci then
      let arg := match l.lit with
        | .app _ #[.app _ #[a]] => a
        | a => a
      sendDtConflict #[l.lit, Node.eqNode arg c] "DATATYPES_TESTER_CONFLICT"
      return
  for j in [0:← numSelApps n] do
    collapseSelector (← selAppAt n j) c
  setInfo n fun e => { e with constructor := some c }

/-- `addTester`: the tester literal `t` (of constructor `tIndex`, on `tArg`) for
the class of `n`. -/
def addTester (tIndex : Nat) (t n tArg : Node) : EEM Unit := do
  let tpol := !isNot t
  let eqc ← eqcInfo? n
  let mut j : Option Node := none
  let mut jt : Node := default
  let mut makeConflict := false
  match ← getLabelIndex eqc n with
  | some ptu =>
    if (ptu == tIndex) != tpol then
      if let some { constructor := some c, .. } := eqc then
        sendDtConflict #[t, Node.eqNode tArg c] "DATATYPES_TESTER_CONFLICT"
        return
      makeConflict := true
      j ← getLabel n
      jt := j.getD default
    else return
  | none =>
    let nl ← numLabels n
    for i in [0:nl] do
      let l ← labelAt n i
      if l.index == tIndex then
        if tpol then
          j := some l.lit
          jt := match l.lit with
            | .app _ #[a] => a
            | a => a
          makeConflict := true
          break
        else return
    if !makeConflict then
      modifyDt fun d => (d.setLabels n (nl + 1)).setLabelData n nl { lit := t, arg := tArg, index := tIndex }
      let nl := nl + 1
      let some T := dtType? tArg | return
      if tpol then
        let _ ← instantiate n
      else if nl == numConstructors T - 1 then
        let pcons ← getPossibleCons (← eqcInfo? n) n T
        let testerIndex := (pcons.toList.idxOf? true).getD 0
        let mut nb : Array Node := #[]
        let mut eqTerms : Array Node := #[]
        for i in [0:nl] do
          let l ← labelAt n i
          nb := nb.push l.lit
          if !eqTerms.contains l.arg then
            eqTerms := eqTerms.push l.arg
            if l.arg != tArg then nb := nb.push (Node.eqNode l.arg tArg)
        let exp := if nb.size == 1 then nb[0]! else .app (.kind .AND) nb
        addPendingInference (mkTester tArg T testerIndex) "DATATYPES_LABEL_EXH" exp
        return
  if makeConflict then
    let some jl := j | return
    let mut conf := #[jl, t]
    let jarg := match jt with
      | .app _ #[a] => a
      | a => a
    if jarg != tArg then conf := conf.push (Node.eqNode jarg tArg)
    sendDtConflict conf "DATATYPES_TESTER_MERGE_CONFLICT"

/-- `merge`: the class of `t₂` is merged into the class of `t₁`. -/
def merge (t₁ t₂ : Node) : EEM Unit := do
  if ← inConflict then return
  let some eqc₂ ← eqcInfo? t₂ | return
  let mut checkInst := false
  match ← eqcInfo? t₁ with
  | some eqc₁ =>
    match eqc₁.constructor, eqc₂.constructor with
    | some c₁, some c₂ =>
      let unifEq := Node.eqNode c₁ c₂
      if checkClash c₁ c₂ then
        sendDtConflict #[unifEq] "DATATYPES_CLASH_CONFLICT"
        return
      if let (some (_, _, as), some (_, _, bs)) := (consApp? c₁, consApp? c₂) then
        for i in [0:as.size] do
          if !(← areEqual as[i]! bs[i]!) then
            addPendingInference (Node.eqNode as[i]! bs[i]!) "DATATYPES_UNIF" unifEq
    | _, _ => pure ()
    setInfo t₁ fun e => { e with inst := e.inst || eqc₂.inst }
    if let some c₂ := eqc₂.constructor then
      if eqc₁.constructor.isNone then
        checkInst := true
        addConstructor c₂ t₁
        if ← inConflict then return
  | none =>
    let _ ← makeEqcInfo t₁
    setInfo t₁ fun _ => { inst := eqc₂.inst, constructor := eqc₂.constructor, selectors := eqc₂.selectors }
  -- the labels
  if (← st).labels.contains ⟨t₂⟩ then
    for i in [0:← numLabels t₂] do
      let l ← labelAt t₂ i
      addTester l.index l.lit t₁ l.arg
      if ← inConflict then return
  -- the selectors
  let e₁ := (← st).getEqcInfo t₁
  if !e₁.selectors && eqc₂.selectors then
    setInfo t₁ fun e => { e with selectors := true }
    checkInst := true
  if (← st).selApps.contains ⟨t₂⟩ then
    for j in [0:← numSelApps t₂] do
      addSelector (← selAppAt t₂ j) t₁ eqc₂.constructor.isNone
  if checkInst then
    let _ ← instantiate t₁

/-- `eqNotifyNewClass`. -/
def notifyNewClass (n : Node) : EEM Unit := do
  if let some (_, _, cs) := consApp? n then
    let _ ← makeEqcInfo n
    if cs.size > 0 then modifyDt fun d => { d with functionTerms := d.functionTerms.push n }
  if let some (_, _, _, a) := selApp? n then
    modifyDt fun d => { d with functionTerms := d.functionTerms.push n }
    let r ← rep a
    let _ ← makeEqcInfo r
    addSelector n r

/-- The theory's handling of the central equality engine's notifications. -/
def handle : Note → EEM Unit
  | .newClass t => notifyNewClass t
  | .merge t₁ t₂ => if (dtType? t₁).isSome then merge t₁ t₂ else pure ()
  | _ => pure ()

/-- The hook of the central equality engine (`EE.Ctx.onNote`): the
notification handled with the context `c` (whose own hook is not used, as the
handlers do not assert to the engine). -/
def onNote (c : Ctx) (n : Note) (ee : EqualityEngine) : EqualityEngine :=
  if ee.dt.enabled then (((handle n).run c).run ee).2 else ee

/-! ## Facts -/

/-- `notifyFact`: a tester literal labels the class of its argument. -/
partial def notifyFact (atom : Node) (pol : Bool) (fact : Node) (isInternal : Bool)
    (process : EEM Unit) : EEM Unit := do
  if let some (tIndex, tArg) := isTester? atom then
    let r ← rep tArg
    let _ ← makeEqcInfo r
    let tst := if isInternal then (if pol then atom else Node.notNode atom) else fact
    addTester tIndex tst r tArg
  if !isInternal then process

/-- Whether a literal holds in the engine (`ProofEqEngine::holds`). -/
def holds (atom : Node) (pol : Bool) : EEM Bool := do
  match atom with
  | .app (.kind .EQUAL) #[a, b] =>
    if !(← hasTerm a) || !(← hasTerm b) then return false
    if pol then areEqual a b else areDisequal a b false
  | _ =>
    if !(← hasTerm atom) then return false
    areEqual atom (if pol then Node.mkTrue else Node.mkFalse)

mutual
  /-- `processInternalFact`: the fact is asserted to the engine with its
  explanation as its reason, unless it holds already, and the theory is
  notified of it. -/
  partial def assertInternalFact (i : Inference) : EEM Unit := do
    prepareDtInference i.conc i.id
    let (atom, pol) := match i.conc with
      | .app (.kind .NOT) #[a] => (a, false)
      | c => (c, true)
    note (.fact dtTheory i.id i.conc i.exp)
    modifyDt fun d => { d with sentFacts := d.sentFacts + 1, facts := d.facts.insert ⟨i.conc⟩ (i.id, i.exp) }
    if !(← holds atom pol) then
      match atom with
      | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol i.exp
      | _ => let _ ← assertPredicate atom pol i.exp
    notifyFact atom pol i.exp true process

  /-- `InferenceManager::process`: the pending lemmas, then the pending facts;
  nothing in a conflict. -/
  partial def process : EEM Unit := do
    if ← inConflict then
      reset
      clearPending
      return
    -- the pending lemmas
    if !(← st).processingLemmas then
      modifyDt fun d => { d with processingLemmas := true }
      let mut i := 0
      while i < (← st).pendingLemmas.size do
        let l := (← st).pendingLemmas[i]!
        let _ ← sendLemma l.conc l.exp l.id
        i := i + 1
      modifyDt fun d => { d with pendingLemmas := #[], processingLemmas := false }
    -- the pending facts
    let mut i := 0
    while !(← inConflict) && i < (← st).pendingFacts.size do
      assertInternalFact (← st).pendingFacts[i]!
      i := i + 1
    modifyDt fun d => { d with pendingFacts := #[] }
end

/-! ## Registration and checks -/

/-- `preRegisterTerm`. -/
def preRegisterTerm (n : Node) : EEM Unit := do
  match n with
  | .app (.kind .EQUAL) _ => UF.addTriggerPredicate n
  | _ => if (isTester? n).isSome then UF.addTriggerPredicate n else addTerm n
  process

/-- The classes of the engine, in the order of their representatives' ids
(`EqClassesIterator`). -/
def classes : EEM (Array Node) := do
  let s ← get
  let mut out := #[]
  for i in [0:s.nodes.size] do
    if find s i == i && !s.isInternal[i]! then out := out.push s.nodes[i]!
  return out

structure CycleState where
  visited : Std.HashSet Key := {}
  proc : Std.HashSet Key := {}
  expl : Array Node := #[]
  /-- The cycle, innermost first: each term, its class's constructor term, and
  the child position that continues the cycle. -/
  path : Array (Node × Node × Nat) := #[]

/-- `searchForCycle`. -/
partial def searchForCycle (n on : Node) (firstTime : Bool) : StateT CycleState EEM (Option Node) := do
  let nn ← rep n
  if !firstTime && nn == on then
    if n != nn then modify fun c => { c with expl := c.expl.push (Node.eqNode n nn) }
    return some on
  if (← get).proc.contains ⟨nn⟩ then return none
  if !(← get).visited.contains ⟨nn⟩ then
    modify fun c => { c with visited := c.visited.insert ⟨nn⟩ }
    let nncons ← getEqcConstructor nn
    if let some (_, _, cs) := consApp? nncons then
      for h : i in [0:cs.size] do
        let c := cs[i]
        let cn ← searchForCycle c on false
        if cn == some on then
          if n != nncons then modify fun c => { c with expl := c.expl.push (Node.eqNode n nncons) }
          modify fun c => { c with path := c.path.push (n, nncons, i) }
          return some on
        else if cn.isSome then return cn
    modify fun c => { c with proc := c.proc.insert ⟨nn⟩, visited := c.visited.erase ⟨nn⟩ }
    return none
  else
    return if (dtType? nn).isSome then some nn else none

/-- `checkCycles`. -/
def checkCycles : EEM Unit := do
  let mut cs : CycleState := {}
  for eqc in ← classes do
    if (dtType? eqc).isNone then continue
    let (cn, cs') ← (searchForCycle eqc eqc true).run cs
    cs := cs'
    let mut cn := cn
    if let some c := cn then
      if c != eqc then
        let (cn', cs') ← (searchForCycle c c true).run {}
        cs := cs'
        cn := cn'
    if cn.isSome then
      sendDtConflict cs.expl "DATATYPES_CYCLE" cs.path
      return

/-- One class of `checkSplit`: whether it sent a lemma (which ends the
splits). -/
def splitStep (n : Node) : EEM Bool := do
  let some T := dtType? n | return false
  let eqc ← eqcInfo? n
  if ← hasLabel eqc n then return false
  let pcons ← getPossibleCons eqc n T
  for j in [0:pcons.size] do
    if !pcons[j]! then continue
    if !(consCardClass T j).isFinite then
      match eqc with
      | some { selectors := true, .. } => pure ()
      | _ => return false
  if numConstructors T == 1 then
    addPendingInference (mkTester n T 0) "DATATYPES_SPLIT" Node.mkTrue
    return false
  sendLemma (mkSplit n T) Node.mkTrue "DATATYPES_SPLIT"

/-- `checkSplit`, within the engine: see the theory engine's `dtPostCheck`,
which sends the lemma of a class before going on, as its atoms are
preregistered then. -/
def checkSplit : EEM Unit := do
  for n in ← classes do
    if ← splitStep n then return

/-- `preCheck`. -/
def preCheck : EEM Unit := do
  process
  reset

/-- `postCheck`; `needCheck` is whether a lemma was sent in this round of
checks (`TheoryEngine::needCheck`). -/
def postCheck (full : Bool) : EEM Unit := do
  process
  if !full || (← inConflict) || (← st).sentLemmas > 0 || (← st).lemmasAdded then return
  repeat
    reset
    checkCycles
    process
    if (← inConflict) || (← st).sentLemmas > 0 then return
    if (← st).sentFacts == 0 then
      reset
      checkSplit
      if (← st).sentLemmas > 0 then modifyDt fun d => { d with pendingFacts := #[] }
      else process
    let d ← st
    if (← inConflict) || d.sentLemmas > 0 || d.sentFacts == 0 then break

/-- `Theory::check`'s processing of one fact: asserted to the engine, with the
fact as its reason, then notified. -/
def assertFact (fact : Node) : EEM Unit := do
  let (atom, pol) := match fact with
    | .app (.kind .NOT) #[a] => (a, false)
    | _ => (fact, true)
  match atom with
  | .app (.kind .EQUAL) _ => let _ ← assertEquality atom pol fact
  | _ => let _ ← assertPredicate atom pol fact
  notifyFact atom pol fact false process

/-- The kinds the theory adds to the equality engine (`finishInit`). -/
def congruenceKind (k : Kind) : Bool :=
  k == .APPLY_CONSTRUCTOR || k == .APPLY_SELECTOR || k == .APPLY_TESTER

end Telos.Solver.DT
