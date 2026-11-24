import Telos.Solver.Theory.QuantInst

/-!
# E-matching

cvc5's `InstantiationEngine` with its strategy of automatic triggers
(`InstStrategyAutoGenTriggers`), its match generators (`InstMatchGenerator`,
`InstMatchGeneratorSimple`, `InstMatchGeneratorMultiLinear`) and candidate
generators (`candidate_generator.cpp`), in the configuration of safe mode
(`docs/theory-engine-plan.md`, Stage 10, step 2). The triggers and their
generators are built in `QuantTrigger.lean`.

A round (`doInstantiationRound`) asks the strategy of each asserted formula at
efforts `0, 1, …`: triggers are made at effort `1` the first time, then every
third round (`incrementTriggers`); every active trigger adds its instances,
once a round. A trigger first purifies its ground terms that the equality
engine does not have (`QUANTIFIERS_GT_PURIFY`).

Not ported yet: user patterns, the regeneration of multi-triggers with their
relational and arithmetic triggers, the
candidate generators of datatypes (selectors, constructors of a datatype with
one constructor), terms for a type when there is no candidate.
-/

namespace Telos.Solver.Quant

/-- The state of matching a trigger: its generators, the match (`InstMatch`),
and the round's data. -/
structure GSt where
  gens : Array Gen
  m : Array (Option Node)
  rd : Round
  q : Node
  id : String
  added : Nat := 0
  deriving Inhabited

abbrev GM := StateT GSt EM

def gctx : GM Ctx := (ectx : EM Ctx)

def tdb (x : M α) : GM α := do
  let rd := (← get).rd
  let (a, rd) ← (runM rd x : EM _)
  modify fun s => { s with rd }
  return a

def inConflict : GM Bool := return (← get).rd.inConflict

def gen (g : Nat) : GM Gen := return (← get).gens[g]!
def modGen (g : Nat) (f : Gen → Gen) : GM Unit := modify fun s => { s with gens := s.gens.modify g f }

/-- `InstMatch::set`: a variable already set must be equal. -/
def imSet (i : Nat) (n : Node) : GM Bool := do
  match (← get).m[i]! with
  | some v => return (← gctx).areEqual v n
  | none =>
    modify fun s => { s with m := s.m.set! i (some n) }
    return true

def imReset (i : Nat) : GM Unit := modify fun s => { s with m := s.m.set! i none }
def imResetAll : GM Unit := modify fun s => { s with m := s.m.map fun _ => none }

/-- `Trigger::sendInstantiation`, then `Instantiate::addInstantiation`. (A
variable left unbound has no term yet: the instance is not sent.) -/
def sendInst (terms : Array (Option Node)) : GM Bool := do
  -- a variable not bound (by a user pattern): a term of its type
  let vs := quantVars (← get).q
  let mut ts : Array Node := #[]
  for i in [0:terms.size] do
    match terms[i]! with
    | some t => ts := ts.push t
    | none =>
      let some t ← tdb (getTermForType (vs[i]?.bind (·.typeHint))) | return false
      ts := ts.push t
  let s ← get
  let (ok, rd) ← (addInstantiation s.rd s.q ts s.id : EM _)
  modify fun s => { s with rd }
  return ok

/-! ## Candidate generators -/

def isLegal (n : Node) : GM Bool := tdb (isTermActive n)

def isLegalOp (op n : Node) : GM Bool := do
  let opm ← tdb (getMatchOperator n)
  if opm == some op then isLegal n else return false

/-- `CandidateGenerator::reset`. -/
def cgReset (k : CGKind) (eqc : Option Node) : GM CGState := do
  let c ← gctx
  match k with
  | .qe op exclude =>
    match eqc with
    | none =>
      let l := ((← tdb getSt).opTerms.get? ⟨op⟩).getD #[]
      return { mode := if l.isEmpty then .none else .db, list := l }
    | some e =>
      if exclude.contains e then return {}
      if c.hasTerm e then
        let tat ← tdb (computeUfEqcTerms op)
        if (tat.find? c.lt e).isSome then return { mode := .eqc, list := c.members (c.rep e) }
        return {}
      return { mode := .ident, eqc := some e }
  | .litDeq .. => return { list := c.members Node.mkFalse }
  | .all _ => return { list := c.reps, firstTime := true }

/-- `CandidateGenerator::getNextCandidate`. -/
partial def cgNext (k : CGKind) : StateT CGState GM (Option Node) := do
  let c ← (gctx : GM _)
  let st ← get
  match k with
  | .qe op exclude =>
    match st.mode with
    | .db =>
      if st.idx ≥ st.list.size then return none
      let n := st.list[st.idx]!
      set { st with idx := st.idx + 1 }
      if !(← (isLegal n : GM _)) || !(← (tdb (hasTermCurrent n) : GM _)) then return ← cgNext k
      if exclude.isEmpty || !exclude.contains (c.rep n) then return some n
      cgNext k
    | .eqc =>
      if st.idx ≥ st.list.size then return none
      let n := st.list[st.idx]!
      set { st with idx := st.idx + 1 }
      if ← (isLegalOp op n : GM _) then return some n
      cgNext k
    | .ident =>
      let some e := st.eqc | return none
      set { st with eqc := none }
      if ← (isLegalOp op e : GM _) then return some e
      return none
    | .none => return none
  | .litDeq kd typ =>
    if st.idx ≥ st.list.size then return none
    let n := st.list[st.idx]!
    set { st with idx := st.idx + 1 }
    if n.getKind == kd && (n.getChildren[0]?.bind (·.typeHint)) == typ && (← (isLegal n : GM _)) then
      return some n
    cgNext k
  | .all typ =>
    if st.idx ≥ st.list.size then
      -- (`getTermForType` is not ported: no term)
      set { st with firstTime := false }
      return none
    let n := st.list[st.idx]!
    set { st with idx := st.idx + 1 }
    if n.typeHint == typ then
      set { (← get) with firstTime := false }
      return some n
    cgNext k

def nextCand (g : Nat) : GM (Option Node) := do
  let gn ← gen g
  let some k := gn.cg | return none
  let (n, cgs) ← (cgNext k).run gn.cgs
  modGen g fun gn => { gn with cgs }
  return n

/-! ## Match generators -/

mutual
  /-- `InstMatchGenerator::reset`. -/
  partial def emResetGen (g : Nat) (eqc : Option Node) : GM Bool := do
    let gn ← gen g
    if gn.kind == .multi then return true
    let some k := gn.cg | return false
    let c ← gctx
    let eqc := eqc.map c.rep
    let mut eqClass := gn.eqClass
    match gn.eqClassRel with
    | some r =>
      match r with
      | .boundVar .. => if eqc.isSome then eqClass := eqc
      | _ => eqClass := some r
    | none => if eqc.isSome then eqClass := eqc
    let cgs ← cgReset k eqClass
    let ec := eqClass
    modGen g fun gn => { gn with eqClass := ec, cgs, needsReset := false, firstCand := none }
    repeat
      let t ← nextCand g
      match t with
      | none => break
      | some t =>
        if !(← gen g).exclude.contains t then
          modGen g fun gn => { gn with firstCand := some t }
          break
    return (← gen g).firstCand.isSome

  /-- `InstMatchGenerator::getMatch`: match the term `t`, bind the variables
  (undone if the rest fails), and continue. -/
  partial def emGetMatch (g : Nat) (t : Node) : GM Int := do
    let gn ← gen g
    let some mp := gn.matchPattern | return -2
    if gn.cg.isNone then return -2
    let c ← gctx
    let mut success := true
    let mut prev : Array Nat := #[]
    let mcs := mp.getChildren
    let tcs := t.getChildren
    for i in [0:mcs.size] do
      let ct := gn.childTypes[i]!
      if ct ≥ 0 then
        let v := ct.toNat
        let addToPrev := (← get).m[v]!.isNone
        if !(← imSet v tcs[i]!) then
          success := false
          break
        else if addToPrev then prev := prev.push v
      else if ct == -1 then
        if !c.areEqual mcs[i]! tcs[i]! then
          success := false
          break
    if let .boundVar .. := mp then
      if let some ct := gn.childTypes[0]? then
        let v := ct.toNat
        let addToPrev := (← get).m[v]!.isNone
        if !(← imSet v t) then success := false
        else if addToPrev then prev := prev.push v
    if let some r@(.boundVar ..) := gn.eqClassRel then
      let pol := gn.pattern.map (·.getKind) != some .NOT
      let pat := match gn.pattern with
        | some p => if p.getKind == Kind.NOT then p.getChildren[0]! else p
        | none => mp
      let tMatch : Option Node :=
        if pol then (if pat.getKind == .EQUAL then some t else none)
        else if pat.getKind == .EQUAL && t.typeHint == some .boolean then
          some (Node.mkBool !(c.areEqual Node.mkTrue t))
        else none
      if let some tm := tMatch then
        -- (the variable of `eqClassRel`)
        if let some v := (quantVars (← get).q).findIdx? (· == r) then
          let addToPrev := (← get).m[v]!.isNone
          if !(← imSet v tm) then success := false
          else if addToPrev then prev := prev.push v
    let mut ret : Int := -1
    if success then
      for i in [0:gn.children.size] do
        if !(← emResetGen gn.children[i]! (some tcs[gn.childIndex[i]!]!)) then
          success := false
          break
      if success then ret ← emContinue g
    if ret < 0 then
      for v in prev do imReset v
    return ret

  /-- `continueNextMatch`. -/
  partial def emContinue (g : Nat) : GM Int := do
    let gn ← gen g
    match gn.next with
    | some n => emNextMatch n
    | none =>
      if gn.activeAdd then return (if ← sendInst (← get).m then 1 else -1)
      return 1

  /-- `getNextMatch`. -/
  partial def emNextMatch (g : Nat) : GM Int := do
    let gn ← gen g
    if gn.kind == .multi then
      -- `InstMatchGeneratorMultiLinear::emNextMatch`
      for ch in gn.children do
        if !(← emResetGen ch none) then return -2
      let ret ← emContinue g
      if ret > 0 then
        for ch in gn.children do
          if let some mi := (← gen ch).currMatched then
            modGen ch fun gn => { gn with exclude := gn.exclude.push mi }
      return ret
    if gn.needsReset then
      let _ ← emResetGen g gn.eqClass
    modGen g fun gn => { gn with currMatched := none }
    let mut success : Int := -1
    let mut t := (← gen g).firstCand
    repeat
      match t with
      | none => break
      | some tn =>
        if !(← gen g).exclude.contains tn then
          success ← emGetMatch g tn
          if (← gen g).independent && success < 0 then
            modGen g fun gn => { gn with exclude := gn.exclude.push tn }
        if success < 0 then
          t ← if ← inConflict then pure none else nextCand g
        else
          let fc ← nextCand g
          modGen g fun gn => { gn with firstCand := fc }
          break
    let tm := t
    modGen g fun gn => { gn with currMatched := tm }
    if success < 0 then
      let _ ← emResetGen g (← gen g).eqClass
    return success
end

/-- `resetInstantiationRound`, along the chain of generators. -/
partial def resetRoundGen (gens : Array Gen) (g : Nat) : Array Gen :=
  let gn := gens[g]!
  let gens := gens.modify g fun gn =>
    { gn with needsReset := if gn.matchPattern.isSome then true else gn.needsReset, exclude := #[] }
  match gn.next with
  | some n => resetRoundGen gens n
  | none => gens

/-- `InstMatchGenerator::addInstantiations`. -/
partial def genAddInsts (root : Nat) : GM Nat := do
  imResetAll
  let mut n := 0
  repeat
    if (← emNextMatch root) ≤ 0 then break
    n := n + 1
    if ← inConflict then break
    imResetAll
  return n

/-- `InstMatchGeneratorSimple::addInstantiations` below the trie `tat` at the
child `argIndex`. -/
partial def simpleRec (s : Simple) (argIndex : Nat) (tat : Trie) : GM Unit := do
  let c ← gctx
  let cs := s.pat.getChildren
  if argIndex == cs.size then
    let some (t, _) := tat.data[0]? | return
    let mut terms : Array (Option Node) := (← get).m.map fun _ => none
    for (i, v) in s.varNum do
      if v ≥ 0 then terms := terms.set! v.toNat (some t.getChildren[i]!)
    if ← sendInst terms then modify fun st => { st with added := st.added + 1 }
    return
  if let some (_, v) := s.varNum.find? (·.1 == argIndex) then
    if v != -1 then
      for (k, child) in tat.data do
        let vn := v.toNat
        let wasSet := (← get).m[vn]!.isSome
        if !(← imSet vn k) then continue
        if ← inConflict then break
        simpleRec s (argIndex + 1) child
        if !wasSet then imReset vn
        if ← inConflict then break
      return
  let r := c.rep cs[argIndex]!
  if let some child := tat.find? c.lt r then simpleRec s (argIndex + 1) child

def simpleAddInsts (s : Simple) : GM Nat := do
  let c ← gctx
  modify fun st => { st with added := 0 }
  let mut tat : Option Trie := none
  match s.eqc with
  | none =>
    tdb (computeUfTerms s.op)
    tat := (← get).rd.funTrie.get? ⟨s.op⟩
  | some e =>
    let whole ← tdb (computeUfEqcTerms s.op)
    if s.pol then tat := whole.find? c.lt e
    else if !(← inConflict) then
      let r := c.rep e
      for (k, child) in whole.data do
        if k != r then
          imResetAll
          simpleRec s 0 child
          if ← inConflict then break
  if let some t := tat then
    if !(← inConflict) then
      imResetAll
      simpleRec s 0 t
  return (← get).added

/-- `Trigger::addInstantiations`: the ground terms the equality engine does
not have purified (`QUANTIFIERS_GT_PURIFY`), then the instances. -/
def trigAddInsts (rd : Round) (ti : Nat) : EM (Nat × Round) := do
  let tr := (← get).em.trigs[ti]!
  let c ← ectx
  let mut gtAdded := 0
  for gt in tr.groundTerms do
    if !c.hasTerm gt && gt.typeHint != some .boolean then
      let k := Node.skolem .PURIFY #[gt]
      modifyThe Out fun o => { o with skolems := o.skolems.push k }
      let _ ← emitLemma { id := "QUANTIFIERS_GT_PURIFY", lem := Node.eqNode k gt }
      gtAdded := gtAdded + 1
  let st : GSt := { gens := tr.gens, m := Array.replicate (quantVars tr.q).size none, rd, q := tr.q, id := tr.id }
  let (n, st) ← (match tr.root with
    | .simple s => simpleAddInsts s
    | .gen r => genAddInsts r).run st
  modify fun e => { e with em := { e.em with trigs := e.em.trigs.modify ti fun t => { t with gens := st.gens } } }
  return (gtAdded + n, st.rd)

/-- `Trigger::resetInstantiationRound` and `reset(null)`. -/
def trigReset (rd : Round) (ti : Nat) : EM Round := do
  let tr := (← get).em.trigs[ti]!
  match tr.root with
  | .simple _ => return rd
  | .gen r =>
    let gens := resetRoundGen tr.gens r
    let st : GSt := { gens, m := Array.replicate (quantVars tr.q).size none, rd, q := tr.q, id := tr.id }
    let (_, st) ← (emResetGen r none).run st
    modify fun e => { e with em := { e.em with trigs := e.em.trigs.modify ti fun t => { t with gens := st.gens } } }
    return st.rd

/-! ## The strategy of automatic triggers -/

def emSel (q : Node) : EM Sel := return selOf (← get).em q

def setSel (q : Node) (s : Sel) : EM Unit :=
  modify fun e => { e with em := { e.em with sel := e.em.sel.insert ⟨q⟩ s } }

/-- Run a selection on `q`'s state. -/
def onSel (q : Node) (x : SelM α) : EM α := do
  let (a, s) := x.run (← emSel q)
  setSel q s
  return a

/-- `generatePatternTerms`: the trigger terms of `q` with all its variables
(single) and with some (multi); false if they do not bind all its variables. -/
def generatePatternTerms (q : Node) : EM Bool := do
  if (← get).em.patTerms.contains ⟨q⟩ then return true
  modify fun e => { e with em := { e.em with patTerms := e.em.patTerms.insert ⟨q⟩ (#[], #[]) } }
  let c ← ectx
  let nvars := (quantVars q).size
  let pats ← onSel q (collectPatTerms c.lt nvars (quantBody q))
  let mut vc : Std.HashSet Nat := {}
  for (_, ti) in pats do
    for v in ti.fv do vc := vc.insert v
  modify fun e => { e with em := { e.em with numTrigVars := e.em.numTrigVars.insert ⟨q⟩ vc.size } }
  if vc.size > 0 && vc.size < nvars then return false
  let mut single : Array Node := #[]
  let mut multi : Array Node := #[]
  for (pat0, ti) in pats do
    let mut pat := pat0
    let rel ← onSel q (usableRelationTrigger pat)
    let adHoc := isRelationalTrigger pat && rel.isNone
    let mut extra : Option Node := none
    if ti.reqPol != 0 then
      if adHoc then pat := if ti.reqPol == -1 then negate pat else pat
      else if pat.typeHint == some .boolean && ti.reqPolEq.isNone then
        -- `literal-match=use`
        pat := Node.notNode (Node.eqNode pat (Node.mkBool (ti.reqPol == -1)))
      else if let some e := ti.reqPolEq then
        if ti.reqPol == -1 then pat := Node.notNode (Node.eqNode pat e)
    else if adHoc then extra := some (negate pat)
    for p in extra.toList ++ [pat] do
      if ti.fv.size == nvars then single := single.push p else multi := multi.push p
  let sm := (single, multi)
  modify fun e => { e with em := { e.em with patTerms := e.em.patTerms.insert ⟨q⟩ sm } }
  return true

/-- The user patterns of `q` (`INST_PATTERN`), each a list of terms. -/
def userPatterns (q : Node) : Array (Array Node) :=
  match q.getChildren[2]? with
  | some l => l.getChildren.filterMap fun p => if p.getKind == .INST_PATTERN then some p.getChildren else none
  | none => #[]

/-- `QuantAttributes::hasPattern`: a pattern, or a term excluded. -/
def hasPatternAttr (q : Node) : Bool :=
  match q.getChildren[2]? with
  | some l => l.getChildren.any fun p => p.getKind == .INST_PATTERN || p.getKind == .INST_NO_PATTERN
  | none => false

/-- `TriggerDatabase::mkTrigger` on the terms `trNodes`, kept: new
(`TR_MAKE_NEW`), or the one made before (`getOld`), or none if there is one
(`returnNull`). -/
inductive TrOption where
  | makeNew | getOld | returnNull

def mkTriggerOf (q : Node) (trNodes : Array Node) (opt : TrOption) (user : Bool := false) : EM (Option Nat) := do
  let s ← emSel q
  let c ← ectx
  let key : Key × List Key := (⟨q⟩, (trNodes.qsort (selLt c.lt s)).toList.map (⟨·⟩))
  if let some t := (← get).em.trie.get? key then
    match opt with
    | .getOld => return some t
    | .returnNull => return none
    | .makeNew => pure ()
  -- the trigger, built (its generators' operators through the term database)
  let ((tr, s'), _) ← runM {} ((mkTrig q trNodes).run s)
  setSel q s'
  let ti := (← get).em.trigs.size
  modify fun e => { e with em := { e.em with trigs := e.em.trigs.push tr, trie := e.em.trie.insert key ti } }
  let tag := match tr.root with
    | .simple _ => "simple"
    | .gen _ => if trNodes.size > 1 then "multi" else ""
  modifyThe Out fun o => { o with triggers := o.triggers.push (o.lemmas.size, .trigger q trNodes tag user) }
  return some ti

/-- `TriggerDatabase::mkTrigger`: the trigger of the terms (those needed to
bind the variables), new, or (`getOld`) the one made before, or none if it was
made (`TR_RETURN_NULL`). -/
def mkTrigger (q : Node) (nodes : Array Node) (getOld : Bool) : EM (Option Nat) := do
  let nv := (quantVars q).size
  let useN := ((← get).em.numTrigVars.get? ⟨q⟩).getD 0
  let nvars := if useN == 0 then nv else useN
  let some trNodes ← onSel q (mkTriggerTerms nodes nvars) | return none
  mkTriggerOf q trNodes (if getOld then .getOld else .returnNull)


/-- `InstStrategyUserPatterns::addUserPattern`: the trigger of a user pattern,
its terms usable (`getIsUsableTrigger`), or none if one is not. -/
def addUserPattern (q : Node) (pat : Array Node) : EM Unit := do
  let mut nodes : Array Node := #[]
  for p in pat do
    if nodes.contains p then continue
    let some u ← onSel q (getIsUsableTrigger p) | return
    nodes := nodes.push u
  if let some t ← mkTriggerOf q nodes .makeNew true then
    modify fun e => { e with em := { e.em with
      userGen := e.em.userGen.insert ⟨q⟩ (((e.em.userGen.get? ⟨q⟩).getD #[]).push t) } }

/-- `InstantiationEngine::registerQuantifier`: the triggers of its user
patterns (its excluded terms are in its selection state, `selOf`). -/
def ematchRegister (q : Node) : EM Unit := do
  for p in userPatterns q do addUserPattern q p

/-- `InstStrategyUserPatterns::process` (`user-pat=trust`): at effort `1`, the
instances of the user triggers; true if unfinished. -/
def processUser (rd : Round) (q : Node) (e : Nat) : EM (Bool × Round) := do
  if e == 0 then return (true, rd)
  if e != 1 then return (false, rd)
  let mut rd := rd
  for ti in ((← get).em.userGen.get? ⟨q⟩).getD #[] do
    let (_, rd') ← trigAddInsts rd ti
    rd := rd'
    if rd.inConflict then break
  return (false, rd)

/-- `addTrigger`. -/
def addTrigger (rd : Round) (q : Node) (ti : Nat) : EM Round := do
  let multi := (← get).em.trigs[ti]!.nodes.size > 1
  let (s, m) := ((← get).em.agt.get? ⟨q⟩).getD (#[], #[])
  let (s, m) := if multi then (s, m.map fun (t, _) => (t, false)) else (s, m)
  let l := if multi then m else s
  let mut rd := rd
  let mut l := l
  if !l.any (·.1 == ti) then
    rd ← trigReset rd ti
    l := (l.push (ti, true)).qsort (·.1 < ·.1)
  l := l.map fun (t, a) => if t == ti then (t, true) else (t, a)
  let v := if multi then (s, l) else (l, m)
  modify fun e => { e with em := { e.em with agt := e.em.agt.insert ⟨q⟩ v } }
  return rd

/-- `generateTriggers`. -/
def generateTriggers (rd : Round) (q : Node) : EM Round := do
  if !(← generatePatternTerms q) then return rd
  let made := (← get).em.made.contains ⟨q⟩
  modify fun e => { e with em := { e.em with made := e.em.made.insert ⟨q⟩ } }
  let (single, multi) := ((← get).em.patTerms.get? ⟨q⟩).getD (#[], #[])
  let mut rd := rd
  if !made && !single.isEmpty then
    for p in single do
      if let some t ← mkTrigger q #[p] false then rd ← addTrigger rd q t
    return rd
  if multi.isEmpty then return rd
  -- on regeneration, the terms shuffled (in place: `std::shuffle`)
  let mut multi := multi
  if made then
    let (m', g) := shuffle multi (← get).em.rng
    multi := m'
    let sm := (single, m')
    modify fun e => { e with em := { e.em with rng := g, patTerms := e.em.patTerms.insert ⟨q⟩ sm } }
  if let some t ← mkTrigger q multi true then rd ← addTrigger rd q t
  return rd

/-- `InstStrategyAutoGenTriggers::process` at the effort `e` of the round:
true if unfinished. -/
def processQ (rd : Round) (q : Node) (e : Nat) : EM (Bool × Round) := do
  -- (`user-pat=trust`: the user patterns only)
  if !(userPatterns q).isEmpty then return (false, rd)
  if e < 1 then return (true, rd)
  let mut gen := false
  if e == 1 then
    match (← get).em.counter.get? ⟨q⟩ with
    | none =>
      modify fun en => { en with em := { en.em with counter := en.em.counter.insert ⟨q⟩ 0 } }
      gen := true
    | some k =>
      modify fun en => { en with em := { en.em with counter := en.em.counter.insert ⟨q⟩ (k + 1) } }
      gen := (k + 1) % 3 == 0
  else gen := true
  let mut rd := rd
  if gen then
    rd ← generateTriggers rd q
    let (s, m) := ((← get).em.agt.get? ⟨q⟩).getD (#[], #[])
    if (← get).em.counter.get? ⟨q⟩ == some 0 && s.isEmpty && m.isEmpty && !hasPatternAttr q then
      modifyThe Out fun o => { o with triggers := o.triggers.push (o.lemmas.size, .noTrigger q) }
  let (s, m) := ((← get).em.agt.get? ⟨q⟩).getD (#[], #[])
  for l in [s, m] do
    for (ti, active) in l do
      if !active then continue
      if (← get).em.processed.contains (⟨q⟩, ti) then continue
      modify fun en => { en with em := { en.em with processed := en.em.processed.insert (⟨q⟩, ti) } }
      let (_, rd') ← trigAddInsts rd ti
      rd := rd'
      if rd.inConflict then break
    if rd.inConflict then break
  return (false, rd)

/-- `processResetInstantiationRound`: every trigger reset. -/
def ematchResetRound (rd : Round) : EM Round := do
  let mut rd := rd
  for ti in [0:(← get).em.trigs.size] do
    let q := (← get).em.trigs[ti]!.q
    let (s, m) := ((← get).em.agt.get? ⟨q⟩).getD (#[], #[])
    let user := ((← get).em.userGen.get? ⟨q⟩).getD #[]
    if (s ++ m).any (·.1 == ti) || user.contains ti then rd ← trigReset rd ti
  modify fun e => { e with em := { e.em with processed := {} } }
  return rd

/-- `InstantiationEngine::check` at the standard effort of the modules
(`doInstantiationRound`). -/
def ematchCheck (rd : Round) (lastCall : Bool) : EM Round := do
  -- (`shouldProcess`: not the bounded ones of the theory of strings)
  let quants := (← orderedAsserted).filter (!·.isBoundedForall)
  if quants.isEmpty then return rd
  let lastWaiting := (← getThe Out).lemmas.size
  let eLimit := if lastCall then 10 else 2
  let mut e := 0
  let mut finished := false
  let mut rd := rd
  while !finished && e ≤ eLimit do
    finished := true
    for q in quants do
      -- the strategies, in order: user patterns, then automatic triggers
      let (unfinishedU, rd') ← processUser rd q e
      rd := rd'
      if rd.inConflict then return rd
      let (unfinished, rd') ← processQ rd q e
      rd := rd'
      if rd.inConflict then return rd
      if unfinished || unfinishedU then finished := false
    if (← getThe Out).lemmas.size > lastWaiting then finished := true
    e := e + 1
  return rd

end Telos.Solver.Quant
