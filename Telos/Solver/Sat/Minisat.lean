import Std.Data.HashSet
import Telos.Solver.Sat.Basic

/-!
# MiniSat, as cvc5 modified it

A port of cvc5's MiniSat (`src/prop/minisat/core/Solver.cc`), the CDCL(T)
solver of cvc5's `--sat-solver=minisat`, in the configuration telos targets
(proofs on, so level-0 false literals are kept in clauses; not incremental, so
one assertion level; MiniSat's simplifications off, as with proofs):
- two-watched-literal propagation, then the theories' (`propagate`): their
  check, their propagations, with lazy reasons explained when conflict
  analysis needs them (`reason`), and their lemmas, added when MiniSat is busy
  (`updateLemmas`);
- first-UIP conflict analysis with deep minimization (`analyze`,
  `litRedundant`), VSIDS (`activity`, the heap), phase saving, Luby restarts,
  and the reduction of learned clauses (`reduceDB`);
- decisions asked of the theories and the decision engine first
  (`pickBranchLit`, `getNextDecisionRequest`).

The solver is generic in its host's monad `m`: it reaches its state through
`MonadStateOf Solver m`, and the theories through `TheoryProxy m`, cvc5's
`TheoryProxy` as MiniSat calls it. That interface is the boundary that another
CDCL(T) solver (verified, or one with an IPASIR-UP interface) plugs into
(`docs/theory-engine-plan.md`, Stage 6). The host can call `newVar` and
`addClause` from its callbacks, as cvc5's CNF stream does for lemmas.

Clauses are never relocated: a removed clause is marked deleted. MiniSat's
garbage collection only relocates, without changing any order, so the search
is the same.
-/

namespace Telos.Sat

/-- A clause reference: an index in the clause store, or `undef`, or `lazy`
(the reason of a theory propagation, computed when it is needed). -/
abbrev CRef := Nat

def CRef.undef : CRef := 1 <<< 62
def CRef.lazy : CRef := (1 <<< 62) + 1

structure Clause where
  lits : Array Lit
  removable : Bool
  /-- The assertion level of the clause (always 0 here). -/
  level : Nat := 0
  activity : Float := 0
  deleted : Bool := false
  deriving Inhabited

structure VarData where
  reason : CRef := CRef.undef
  level : Int := -1
  trailIndex : Int := -1
  deriving Inhabited

structure Watcher where
  cref : CRef
  blocker : Lit
  deriving Inhabited

/-- The effort of a theory check that MiniSat asks for. -/
inductive Effort where
  | standard
  | full
  deriving BEq, Inhabited

/-- What MiniSat asks of the theories (cvc5's `TheoryProxy`). -/
class TheoryProxy (m : Type → Type) where
  /-- Check the literals asserted so far. -/
  theoryCheck : Effort → m Unit
  /-- The literals the theories propagate. -/
  theoryPropagate : m (Array Lit)
  /-- The explanation of a propagated literal `l`: a clause with `l` first. -/
  explainPropagation : Lit → m (Array Lit)
  /-- A theory literal was assigned. -/
  enqueueTheoryLiteral : Lit → m Unit
  /-- The SAT context: a new decision level, and leaving one. -/
  contextPush : m Unit
  contextPop : m Unit
  /-- Backtracking happened (`notifyBacktrack`). -/
  notifyBacktrack : m Unit
  /-- A decision requested by the theories or the decision engine
  (`Lit.undef` if none), whether its phase is required, and whether to stop
  the search. -/
  getNextDecisionRequest : m (Lit × Bool × Bool)
  isDecisionEngineDone : m Bool
  /-- The theories need another check (`theoryNeedCheck`). -/
  theoryNeedCheck : m Bool
  notifySatClause : Array Lit → m Unit
  notifyRestart : m Unit

structure Solver where
  /-- Keep level-0 false literals in clauses (proofs on). -/
  needProof : Bool := true
  /-- Remove the satisfied problem clauses at level 0 (when MiniSat is not
  incremental: cvc5 makes it incremental with the justification heuristic). -/
  removeSatisfied : Bool := true
  ok : Bool := true
  clauses : Array Clause := #[]
  clausesPersistent : Array CRef := #[]
  clausesRemovable : Array CRef := #[]
  claInc : Float := 1
  activity : Array Float := #[]
  varInc : Float := 1
  watches : Array (Array Watcher) := #[]
  dirty : Array Bool := #[]
  dirties : Array Lit := #[]
  assigns : Array LBool := #[]
  /-- The preferred polarity (bit 0, true for negative) and whether it is
  frozen (bit 1). -/
  polarity : Array Nat := #[]
  decision : Array Bool := #[]
  theory : Array Bool := #[]
  trail : Array Lit := #[]
  trailLim : Array Nat := #[]
  vardata : Array VarData := #[]
  qhead : Nat := 0
  simpDBAssigns : Int := -1
  simpDBProps : Int := 0
  orderHeap : Heap := {}
  seen : Array Bool := #[]
  analyzeStack : Array Lit := #[]
  analyzeToclear : Array Lit := #[]
  maxLearnts : Float := 0
  learntsizeAdjustConfl : Float := 0
  learntsizeAdjustCnt : Int := 0
  lemmas : Array (Array Lit) := #[]
  lemmasRemovable : Array Bool := #[]
  recheck : Bool := false
  theoryConflict : Bool := false
  busy : Bool := false
  model : Array LBool := #[]
  -- parameters (cvc5's defaults)
  varDecay : Float := 0.95
  clauseDecay : Float := 0.999
  randomVarFreq : Float := 0
  randomSeed : Float := 91648253
  restartFirst : Nat := 25
  restartInc : Float := 3
  learntsizeFactor : Float := 1
  learntsizeInc : Float := 1.5
  learntsizeAdjustStartConfl : Nat := 100
  learntsizeAdjustInc : Float := 1.5
  -- statistics
  decisions : Nat := 0
  conflicts : Nat := 0
  propagations : Nat := 0
  decVars : Int := 0
  clausesLiterals : Nat := 0
  learntsLiterals : Nat := 0
  deriving Inhabited

namespace Solver

variable {m : Type → Type} [Monad m] [MonadStateOf Solver m] [TheoryProxy m]

/-- Update the solver in place. -/
@[inline] def upd (f : Solver → Solver) : m Unit := modifyThe Solver f

@[inline] def st : m Solver := getThe Solver

def nVars (s : Solver) : Nat := s.vardata.size

def value (s : Solver) (p : Lit) : LBool := s.assigns[p.var]!.xor p.sign

def valueVar (s : Solver) (v : Var) : LBool := s.assigns[v]!

def level (s : Solver) (v : Var) : Int := s.vardata[v]!.level

def decisionLevel (s : Solver) : Nat := s.trailLim.size

def trailIndex (s : Solver) (v : Var) : Int := s.vardata[v]!.trailIndex

/-- The order of the heap: higher activity first. -/
def heapLt (s : Solver) (x y : Nat) : Bool := s.activity[x]! > s.activity[y]!

/-- `insertVarOrder`. -/
def insertVarOrder (s : Solver) (x : Var) : Solver :=
  if !s.orderHeap.inHeap x && s.decision[x]! then
    let h := s.orderHeap
    let s := { s with orderHeap := {} }
    { s with orderHeap := h.insert (heapLt s) x }
  else s

/-- `setDecisionVar`. -/
def setDecisionVar (s : Solver) (v : Var) (b : Bool) : Solver :=
  let dv := if b && !s.decision[v]! then s.decVars + 1
    else if !b && s.decision[v]! then s.decVars - 1 else s.decVars
  let d := s.decision
  let s := { s with decision := #[] }
  insertVarOrder { s with decision := d.set! v b, decVars := dv } v

/-- `newVar`, on the solver. -/
def addVar (s : Solver) (sign : Bool := true) (dvar : Bool := true) (isTheoryAtom : Bool := false) :
    Var × Solver :=
    let v := s.nVars
    let s := { s with
      watches := (s.watches.push #[]).push #[]
      dirty := (s.dirty.push false).push false
      assigns := s.assigns.push .undef
      vardata := s.vardata.push {}
      activity := s.activity.push 0
      seen := s.seen.push false
      polarity := s.polarity.push (if sign then 1 else 0)
      decision := s.decision.push false
      theory := s.theory.push isTheoryAtom }
    (v, setDecisionVar s v dvar)

/-- `newVar`: a variable with its preferred polarity `sign`, whether it is a
decision variable, and whether it is a theory atom. -/
def newVar (sign : Bool := true) (dvar : Bool := true) (isTheoryAtom : Bool := false) : m Var := do
  modifyGetThe Solver (addVar · sign dvar isTheoryAtom)

/-- `uncheckedEnqueue`: assign `p`, with the reason `from`. -/
def uncheckedEnqueue (p : Lit) (from_ : CRef := CRef.undef) : m Unit := do
  let isTheory ← modifyGetThe Solver fun s =>
    let a := s.assigns
    let vd := s.vardata
    let tr := s.trail
    let s := { s with assigns := #[], vardata := #[], trail := #[] }
    let d : VarData := { reason := from_, level := s.decisionLevel, trailIndex := tr.size }
    (s.theory[p.var]!,
     { s with assigns := a.set! p.var (LBool.ofBool !p.sign), vardata := vd.set! p.var d, trail := tr.push p })
  if isTheory then TheoryProxy.enqueueTheoryLiteral p

/-- The comparison of `lemma_lt`: unassigned literals first, then true ones,
then false ones, the later assigned first among those of the same value. -/
def lemmaLt (s : Solver) (x y : Lit) : Bool :=
  let xv := s.value x
  let yv := s.value y
  if xv == .undef && yv == .undef then x < y
  else if xv == .undef then true
  else if yv == .undef then false
  else if xv == yv then s.trailIndex x.var > s.trailIndex y.var
  else xv == .tt

/-- `attachClause`. -/
def attachClause (s : Solver) (cr : CRef) : Solver :=
  let c := s.clauses[cr]!
  let w := s.watches
  let s := { s with watches := #[] }
  let w := w.modify c.lits[0]!.neg.x (·.push ⟨cr, c.lits[1]!⟩)
  let w := w.modify c.lits[1]!.neg.x (·.push ⟨cr, c.lits[0]!⟩)
  if c.removable then { s with watches := w, learntsLiterals := s.learntsLiterals + c.lits.size }
  else { s with watches := w, clausesLiterals := s.clausesLiterals + c.lits.size }

/-- Allocate a clause. -/
def alloc (s : Solver) (lits : Array Lit) (removable : Bool) : CRef × Solver :=
  let cs := s.clauses
  let s := { s with clauses := #[] }
  (cs.size, { s with clauses := cs.push { lits, removable } })

/-- `isPropagatedBy`, for `locked`. -/
def locked (s : Solver) (cr : CRef) : Bool :=
  let c := s.clauses[cr]!
  let v := c.lits[0]!.var
  s.value c.lits[0]! == .tt && s.vardata[v]!.reason == cr

/-- `detachClause` (not strict: the watchers are removed lazily). -/
def detachClause (s : Solver) (cr : CRef) : Solver :=
  let c := s.clauses[cr]!
  let smudge (s : Solver) (l : Lit) : Solver :=
    if s.dirty[l.x]! then s else
      let d := s.dirty
      let ds := s.dirties
      let s := { s with dirty := #[], dirties := #[] }
      { s with dirty := d.set! l.x true, dirties := ds.push l }
  let s := smudge (smudge s c.lits[0]!.neg) c.lits[1]!.neg
  if c.removable then { s with learntsLiterals := s.learntsLiterals - c.lits.size }
  else { s with clausesLiterals := s.clausesLiterals - c.lits.size }

/-- `removeClause`. -/
def removeClause (s : Solver) (cr : CRef) : Solver :=
  let s := detachClause s cr
  let s := if locked s cr then
      let v := s.clauses[cr]!.lits[0]!.var
      let vd := s.vardata
      let s := { s with vardata := #[] }
      { s with vardata := vd.modify v fun d => { d with reason := CRef.undef } }
    else s
  let cs := s.clauses
  let s := { s with clauses := #[] }
  { s with clauses := cs.modify cr fun c => { c with deleted := true } }

/-- `watches.cleanAll`: drop the watchers of deleted clauses. -/
def cleanAll (s : Solver) : Solver := Id.run do
  let mut w := s.watches
  let mut d := s.dirty
  let ds := s.dirties
  let mut s := { s with watches := #[], dirty := #[], dirties := #[] }
  for l in ds do
    if d[l.x]! then
      let cs := s.clauses
      w := w.modify l.x fun ws => ws.filter fun x => !cs[x.cref]!.deleted
      d := d.set! l.x false
  return { s with watches := w, dirty := d }

/-- `cancelUntil`: backtrack to decision level `lvl`. -/
def cancelUntil (lvl : Nat) : m Unit := do
  let s ← st
  if s.decisionLevel ≤ lvl then return
  for _ in [0:s.trailLim.size - lvl] do TheoryProxy.contextPop
  upd fun s => Id.run do
    let lim := s.trailLim[lvl]!
    let last := s.trailLim.back!
    let mut a := s.assigns
    let mut vd := s.vardata
    let mut pol := s.polarity
    let tr := s.trail
    let mut s := { s with assigns := #[], vardata := #[], polarity := #[], trail := #[] }
    let mut c := tr.size
    while c > lim do
      c := c - 1
      let x := tr[c]!.var
      a := a.set! x .undef
      vd := vd.modify x fun d => { d with trailIndex := -1 }
      -- phase saving (full)
      if pol[x]! &&& 2 == 0 then pol := pol.set! x (if tr[c]!.sign then 1 else 0)
      s := insertVarOrder s x
    let _ := last
    return { s with assigns := a, vardata := vd, polarity := pol, qhead := lim,
                    trail := tr.take lim, trailLim := s.trailLim.take lvl }
  TheoryProxy.notifyBacktrack

/-- `freezePolarity`: the decision heuristic always uses the literal's sign
for its variable (`MinisatSatSolver::preferPhase`). -/
def freezePolarity (s : Solver) (l : Lit) : Solver :=
  { s with polarity := s.polarity.set! l.var ((if l.sign then 1 else 0) ||| 2) }

/-- `varBumpActivity`. -/
def varBumpActivity (s : Solver) (v : Var) : Solver := Id.run do
  let act := s.activity
  let mut s := { s with activity := #[] }
  let mut act := act.modify v (· + s.varInc)
  if act[v]! > 1e100 then
    act := act.map (· * 1e-100)
    s := { s with varInc := s.varInc * 1e-100 }
  s := { s with activity := act }
  if s.orderHeap.inHeap v then
    let h := s.orderHeap
    s := { s with orderHeap := {} }
    s := { s with orderHeap := h.decrease (heapLt s) v }
  return s

/-- `claBumpActivity`. -/
def claBumpActivity (s : Solver) (cr : CRef) : Solver := Id.run do
  let cs := s.clauses
  let mut s := { s with clauses := #[] }
  let mut cs := cs.modify cr fun c => { c with activity := c.activity + s.claInc }
  if cs[cr]!.activity > 1e20 then
    for r in s.clausesRemovable do
      cs := cs.modify r fun c => { c with activity := c.activity * 1e-20 }
    s := { s with claInc := s.claInc * 1e-20 }
  return { s with clauses := cs }

/-- `abstractLevel`. -/
def abstractLevel (s : Solver) (v : Var) : Nat := 1 <<< ((s.level v).toNat % 32)

/-- `reason`: the reason of `x`, explaining a theory propagation (a lazy
reason) as a clause, which is added. -/
def reason (x : Var) : m CRef := do
  let s ← st
  let r := s.vardata[x]!.reason
  if r != CRef.lazy then return r
  let l := Lit.mk x (s.valueVar x != .tt)
  let expl ← TheoryProxy.explainPropagation l
  modifyGetThe Solver fun s => Id.run do
    let expl := sort (lemmaLt s) expl
    -- drop duplicates and level-0 literals, after the first
    let mut out : Array Lit := #[]
    let mut prev := Lit.undef
    for i in [0:expl.size] do
      let e := expl[i]!
      if i == 0 then
        out := out.push e
        prev := e
        continue
      if e == prev then continue
      if s.level e.var == 0 then continue
      out := out.push e
      prev := e
    if out.size == 1 then out := out.push (Lit.mk 0 true)
    let (cr, s) := alloc s out true
    let vd := s.vardata
    let s := { s with vardata := #[] }
    let s := { s with vardata := vd.modify x fun d => { d with reason := cr },
                      clausesRemovable := s.clausesRemovable.push cr }
    (cr, attachClause s cr)

/-- `SatProofManager::explainLit`, for the explanations it asks of the
theories: the reason of the true literal `p` (which a theory explains, if it
propagated `p`), then, recursively, of the other literals of that reason; the
literals in `seen` are explained already. -/
partial def explainLitPf (p : Lit) (seen : Std.HashSet Var) : m (Std.HashSet Var) := do
  if seen.contains p.var then return seen
  let mut seen := seen.insert p.var
  let r ← reason p.var
  if r == CRef.undef then return seen
  let c := (← st).clauses[r]!
  for q in c.lits do
    if q.var == p.var then continue
    seen ← explainLitPf q.neg seen
  return seen

/-- `SatProofManager::finalizeProof` on the clause `c` in conflict at level 0
(with proofs): the negations of its literals are explained (`explainLitPf`).
(cvc5 then explains the remaining leaves of its proof of `false`; telos
explains the theory propagations at level 0 after the refutation, quietly.) -/
def finalizeExplain (c : Array Lit) : m Unit := do
  if !(← st).needProof then return
  let mut seen : Std.HashSet Var := {}
  for q in c do seen ← explainLitPf q.neg seen

/-- `litRedundant`. -/
partial def litRedundant (p : Lit) (abstractLevels : Nat) : m Bool := do
  upd fun s => { s with analyzeStack := #[p] }
  let top := (← st).analyzeToclear.size
  let rec loop : m Bool := do
    let s ← st
    if s.analyzeStack.isEmpty then return true
    let q := s.analyzeStack.back!
    let cr ← reason q.var
    upd fun s => { s with analyzeStack := s.analyzeStack.pop }
    let c := (← st).clauses[cr]!
    for i in [1:c.lits.size] do
      let p2 := c.lits[i]!
      let s ← st
      if !s.seen[p2.var]! && s.level p2.var > 0 then
        let r2 ← reason p2.var
        let s ← st
        if r2 != CRef.undef && (abstractLevel s p2.var &&& abstractLevels) != 0 then
          upd fun s => { s with seen := s.seen.set! p2.var true,
                                analyzeStack := s.analyzeStack.push p2,
                                analyzeToclear := s.analyzeToclear.push p2 }
        else
          upd fun s => Id.run do
            let mut sn := s.seen
            for j in [top:s.analyzeToclear.size] do sn := sn.set! s.analyzeToclear[j]!.var false
            return { s with seen := sn, analyzeToclear := s.analyzeToclear.take top }
          return false
    loop
  loop

/-- `analyze`: the learned clause of the conflict `confl` (its asserting
literal first, a literal of the next highest level second), and the level to
backtrack to. -/
def analyze (confl : CRef) : m (Array Lit × Nat) := do
  let mut pathC := 0
  let mut p := Lit.undef
  let mut out : Array Lit := #[Lit.undef]
  let mut index : Int := (← st).trail.size - 1
  let mut confl := confl
  repeat
    let c := (← st).clauses[confl]!
    if c.removable then upd fun s => claBumpActivity s confl
    let start := if p == Lit.undef then 0 else 1
    for j in [start:c.lits.size] do
      let q := c.lits[j]!
      let s ← st
      if !s.seen[q.var]! && s.level q.var > 0 then
        upd fun s => { varBumpActivity s q.var with seen := (varBumpActivity s q.var).seen.set! q.var true }
        if (← st).level q.var ≥ (← st).decisionLevel then pathC := pathC + 1
        else out := out.push q
    -- the next literal of the trail to look at
    let s ← st
    while !s.seen[s.trail[index.toNat]!.var]! do index := index - 1
    index := index - 1
    p := s.trail[(index + 1).toNat]!
    confl ← reason p.var
    upd fun s => { s with seen := s.seen.set! p.var false }
    pathC := pathC - 1
    if pathC == 0 then break
  out := out.set! 0 p.neg
  -- deep minimization
  upd fun s => { s with analyzeToclear := out }
  let s ← st
  let mut absLevel := 0
  for i in [1:out.size] do absLevel := absLevel ||| abstractLevel s out[i]!.var
  let mut j := 1
  let mut out' := out
  for i in [1:out.size] do
    let l := out[i]!
    let r ← reason l.var
    if r == CRef.undef then
      out' := out'.set! j l
      j := j + 1
    else if !(← litRedundant l absLevel) then
      out' := out'.set! j l
      j := j + 1
  let mut learnt := out'.take j
  -- the backtrack level
  let s ← st
  let mut bt := 0
  if learnt.size > 1 then
    let mut maxI := 1
    for k in [2:learnt.size] do
      if s.level learnt[k]!.var > s.level learnt[maxI]!.var then maxI := k
    let p2 := learnt[maxI]!
    learnt := (learnt.set! maxI learnt[1]!).set! 1 p2
    bt := (s.level p2.var).toNat
  upd fun s => Id.run do
    let mut sn := s.seen
    for l in s.analyzeToclear do sn := sn.set! l.var false
    return { s with seen := sn }
  return (learnt, bt)

/-- `propagateBool`: two-watched-literal propagation; a conflicting clause, or
`undef`. -/
def propagateBool : m CRef := do
  upd cleanAll
  let mut confl := CRef.undef
  let mut numProps := 0
  repeat
    let s ← st
    if s.qhead ≥ s.trail.size then break
    let p := s.trail[s.qhead]!
    upd fun s => { s with qhead := s.qhead + 1 }
    numProps := numProps + 1
    -- take the watchers of p out
    let ws ← modifyGetThe Solver fun s =>
      let w := s.watches
      let s := { s with watches := #[] }
      (w[p.x]!, { s with watches := w.set! p.x #[] })
    let mut kept : Array Watcher := #[]
    let mut i := 0
    while i < ws.size do
      let wt := ws[i]!
      let s ← st
      if s.value wt.blocker == .tt then
        kept := kept.push wt
        i := i + 1
        continue
      let cr := wt.cref
      let falseLit := p.neg
      -- make sure the false literal is second
      let c0 := s.clauses[cr]!.lits
      let c := if c0[0]! == falseLit then (c0.set! 0 c0[1]!).set! 1 falseLit else c0
      i := i + 1
      let first := c[0]!
      let w : Watcher := ⟨cr, first⟩
      upd fun s =>
        let cs := s.clauses
        let s := { s with clauses := #[] }
        { s with clauses := cs.modify cr fun cl => { cl with lits := c } }
      if first != wt.blocker && s.value first == .tt then
        kept := kept.push w
        continue
      -- look for a new watch
      let mut found := false
      for k in [2:c.size] do
        if s.value c[k]! != .ff then
          let c' := (c.set! 1 c[k]!).set! k falseLit
          upd fun s =>
            let cs := s.clauses
            let wts := s.watches
            let s := { s with clauses := #[], watches := #[] }
            { s with clauses := cs.modify cr fun cl => { cl with lits := c' },
                     watches := wts.modify c'[1]!.neg.x (·.push w) }
          found := true
          break
      if found then continue
      kept := kept.push w
      if s.value first == .ff then
        confl := cr
        upd fun s => { s with qhead := s.trail.size }
        while i < ws.size do
          kept := kept.push ws[i]!
          i := i + 1
      else
        uncheckedEnqueue first cr
    -- the watchers kept, then those added meanwhile
    upd fun s =>
      let w := s.watches
      let s := { s with watches := #[] }
      { s with watches := w.modify p.x fun added => kept ++ added }
  upd fun s => { s with propagations := s.propagations + numProps,
                        simpDBProps := s.simpDBProps - numProps }
  return confl

/-- `updateLemmas`: add the lemmas the theories sent, backtracking if needed;
a conflict, or `undef`. -/
def updateLemmas : m CRef := do
  let mut conflict := CRef.undef
  let mut backtrackLevel := (← st).decisionLevel
  -- the backtrack level, over the lemmas (sorted)
  let mut i := 0
  repeat
    let s ← st
    if i ≥ s.lemmas.size then break
    while i < (← st).lemmas.size do
      let s ← st
      let lemma := sort (lemmaLt s) s.lemmas[i]!
      upd fun s => { s with lemmas := s.lemmas.set! i lemma }
      if lemma.size == 0 then
        conflict := CRef.lazy
        backtrackLevel := 0
      else if lemma.size == 1 || s.value lemma[1]! == .ff then
        let cur : Nat := if lemma.size == 1 then 0 else (s.level lemma[1]!.var).toNat
        if s.value lemma[0]! != .tt || s.level lemma[0]!.var > cur then
          if cur < backtrackLevel then backtrackLevel := cur
      i := i + 1
    cancelUntil backtrackLevel
  let backtrackIndex := (← st).trail.size
  let lemmas := (← st).lemmas
  let removables := (← st).lemmasRemovable
  for j in [0:lemmas.size] do
    let lemma := lemmas[j]!
    let removable := removables[j]!
    let mut lemmaRef := CRef.undef
    if lemma.size > 1 then
      let cr ← modifyGetThe Solver fun s =>
        let (cr, s) := alloc s lemma removable
        let s := if removable then { s with clausesRemovable := s.clausesRemovable.push cr }
          else { s with clausesPersistent := s.clausesPersistent.push cr }
        (cr, attachClause s cr)
      lemmaRef := cr
    let s ← st
    if conflict == CRef.undef && s.value lemma[0]! != .tt then
      if lemma.size == 1 ||
          (s.value lemma[1]! == .ff && s.trailIndex lemma[1]!.var < backtrackIndex) then
        if s.value lemma[0]! == .ff then
          conflict := if lemma.size > 1 then lemmaRef else CRef.lazy
        else
          uncheckedEnqueue lemma[0]! lemmaRef
  upd fun s => { s with lemmas := #[], lemmasRemovable := #[],
                        theoryConflict := s.theoryConflict || conflict != CRef.undef }
  return conflict

/-- The kind of a propagation (`TheoryCheckType`). -/
inductive CheckType where
  | withoutTheory
  | withTheory
  | final
  deriving BEq

/-- The literals of a clause to add (`addClause_`'s first part): sorted,
without duplicates, and, without proofs, without level-0 false literals; with
the number of false literals; or `none` if it is satisfied (or a tautology). -/
def filterClause (s : Solver) (ps : Array Lit) : Option (Array Lit × Nat) := Id.run do
  let ps := sort (· < ·) ps
  let mut out : Array Lit := #[]
  let mut p := Lit.undef
  let mut falseCount := 0
  for q in ps do
    if q == p.neg then return none
    if s.value q == .tt && s.level q.var == 0 then return none
    if q == p then continue
    if s.value q == .ff then
      if !s.needProof && s.level q.var == 0 then continue
      falseCount := falseCount + 1
    out := out.push q
    p := q
  return some (out, falseCount)

/-- `addClause_` while MiniSat is busy: the clause is queued as a lemma. -/
def queueClause (ps : Array Lit) (removable : Bool) : m Unit := do
  let s ← st
  if !s.ok then return
  match filterClause s ps with
  | none => pure ()
  | some (out, _) =>
    upd fun s => { s with lemmas := s.lemmas.push out, lemmasRemovable := s.lemmasRemovable.push removable }

/-- `propagateTheory`: assign the theories' propagations; a false one is
explained, and its explanation added as a clause. -/
def propagateTheory : m Unit := do
  let lits ← TheoryProxy.theoryPropagate
  for p in lits do
    let s ← st
    if s.value p == .undef then uncheckedEnqueue p CRef.lazy
    else if s.value p == .ff then
      let expl ← TheoryProxy.explainPropagation p
      queueClause expl true

/-- The body of `propagate`. -/
def propagateCore (type : CheckType) : m CRef := do
  if !(← st).lemmas.isEmpty then
    let confl ← updateLemmas
    if confl != CRef.undef then return confl
  if type == .final then
    TheoryProxy.theoryCheck .full
    propagateTheory
    if !(← st).lemmas.isEmpty then
      upd fun s => { s with recheck := true }
      return ← updateLemmas
    let nc ← TheoryProxy.theoryNeedCheck
    upd fun s => { s with recheck := nc }
    return CRef.undef
  let mut confl := CRef.undef
  repeat
    confl ← propagateBool
    if confl == CRef.undef && type != .withoutTheory then
      TheoryProxy.theoryCheck .standard
      propagateTheory
      if !(← st).lemmas.isEmpty then confl ← updateLemmas
    else if !(← st).lemmas.isEmpty then
      let oldLevel := (← st).decisionLevel
      let lemmaConflict ← updateLemmas
      if lemmaConflict != CRef.undef then confl := lemmaConflict
      else if oldLevel > (← st).decisionLevel then confl := CRef.undef
    let s ← st
    if confl != CRef.undef || s.qhead ≥ s.trail.size then break
  return confl

/-- `propagate`: Boolean propagation, then the theories', with their lemmas;
a conflict, or `undef`. MiniSat is busy meanwhile: clauses added are lemmas. -/
def propagate (type : CheckType) : m CRef := do
  upd fun s => { s with recheck := false, theoryConflict := false }
  let wasBusy := (← st).busy
  upd fun s => { s with busy := true }
  let result ← propagateCore type
  upd fun s => { s with busy := wasBusy }
  return result

/-- `addClause_`: while busy, the clause is queued as a lemma. Otherwise, at
level 0, it is added, and a unit propagated. Returns false if the clauses are
then unsatisfiable. -/
def addClause (ps : Array Lit) (removable : Bool) : m Bool := do
  let s ← st
  if !s.ok then return false
  if s.busy then
    queueClause ps removable
    return true
  let some (out, falseCount) := filterClause s ps | return true
  let mut out := out
  if out.size == falseCount then
    if s.needProof then
      if falseCount == 1 then
        finalizeExplain out
        upd fun s => { s with ok := false }
        return false
    else
      upd fun s => { s with ok := false }
      return false
  let mut cr := CRef.undef
  if out.size > 1 then
    let sorted := sort (lemmaLt s) out
    out := sorted
    let r ← modifyGetThe Solver fun s =>
      let (cr, s) := alloc s sorted false
      (cr, attachClause { s with clausesPersistent := s.clausesPersistent.push cr } cr)
    cr := r
    if s.needProof && out.size == falseCount then
      finalizeExplain out
      upd fun s => { s with ok := false }
      return false
  if out.size == falseCount + 1 && (← st).valueVar out[0]!.var == .undef then
    uncheckedEnqueue out[0]! cr
    if out.size == 1 then TheoryProxy.notifySatClause #[out[0]!]
    let confl ← propagate .withoutTheory
    let ok := confl == CRef.undef
    if !ok && confl != CRef.lazy then finalizeExplain (← st).clauses[confl]!.lits
    upd fun s => { s with ok }
    return ok
  return true

/-- `drand`: MiniSat's random numbers. -/
def drand (seed : Float) : Float × Float :=
  let seed := seed * 1389796
  let q := (seed / 2147483647).floor
  let seed := seed - q * 2147483647
  (seed / 2147483647, seed)

/-- `pickBranchLit`: the next decision, asked of the theories first; `undef`
if every decision variable is assigned. -/
def pickBranchLit : m Lit := do
  let (l, rp, stop) ← TheoryProxy.getNextDecisionRequest
  if stop then return Lit.undef
  let mut next := l
  let mut requirePhase := rp
  while next != Lit.undef do
    let s ← st
    let v := next.var
    if !requirePhase && s.polarity[v]! &&& 2 != 0 then next := Lit.mk v (s.polarity[v]! &&& 1 == 1)
    if s.valueVar v == .undef then
      upd fun s => { s with decisions := s.decisions + 1 }
      return next
    let (l, rp, stop) ← TheoryProxy.getNextDecisionRequest
    if stop then return Lit.undef
    next := l
    requirePhase := rp
  -- VSIDS (random decisions are off: the random number is still drawn)
  let (r, seed) := drand (← st).randomSeed
  upd fun s => { s with randomSeed := seed }
  let _ := r
  repeat
    let s ← st
    if s.orderHeap.empty then return Lit.undef
    let (v, h) := s.orderHeap.removeMin (heapLt s)
    upd fun s => { s with orderHeap := h }
    let s ← st
    if v < s.nVars && s.valueVar v == .undef && s.decision[v]! then
      upd fun s => { s with decisions := s.decisions + 1 }
      return Lit.mk v (s.polarity[v]! &&& 1 == 1)
  return Lit.undef

/-- `newDecisionLevel`. -/
def newDecisionLevel : m Unit := do
  upd fun s => { s with trailLim := s.trailLim.push s.trail.size }
  TheoryProxy.contextPush

/-- `reduceDB`: remove half of the learned clauses (not binary, not locked). -/
def reduceDB : m Unit := do
  upd fun s => Id.run do
    let extraLim := s.claInc / s.clausesRemovable.size.toFloat
    let cs := s.clauses
    let lt (x y : CRef) : Bool :=
      cs[x]!.lits.size > 2 && (cs[y]!.lits.size == 2 || cs[x]!.activity < cs[y]!.activity)
    let sorted := sort lt s.clausesRemovable
    let mut s := { s with clausesRemovable := #[] }
    let mut kept : Array CRef := #[]
    for i in [0:sorted.size] do
      let cr := sorted[i]!
      let c := s.clauses[cr]!
      if c.lits.size > 2 && !locked s cr && (i < sorted.size / 2 || c.activity < extraLim) then
        s := removeClause s cr
      else kept := kept.push cr
    return { s with clausesRemovable := kept }

/-- `satisfied`. -/
def satisfied (s : Solver) (cr : CRef) : Bool := s.clauses[cr]!.lits.any (s.value · == .tt)

/-- `rebuildOrderHeap`. -/
def rebuildOrderHeap (s : Solver) : Solver :=
  let vs := (List.range s.nVars).filter (fun v => s.decision[v]! && s.valueVar v == .undef)
  let h := s.orderHeap
  let s := { s with orderHeap := {} }
  { s with orderHeap := h.build (heapLt s) vs.toArray }

/-- `simplify`: at level 0, remove the satisfied learned clauses (and not the
others: MiniSat keeps them when it is incremental, which cvc5's is not, so
they are removed too). -/
def simplify : m Bool := do
  if !(← st).ok then return false
  if (← propagate .withoutTheory) != CRef.undef then
    upd fun s => { s with ok := false }
    return false
  let s ← st
  if s.trail.size == s.simpDBAssigns || s.simpDBProps > 0 then return true
  upd fun s => Id.run do
    let mut s := s
    for list in (if s.removeSatisfied then [true, false] else [true]) do
      let cs := if list then s.clausesRemovable else s.clausesPersistent
      let mut kept := #[]
      for cr in cs do
        if satisfied s cr then s := removeClause s cr else kept := kept.push cr
      s := if list then { s with clausesRemovable := kept } else { s with clausesPersistent := kept }
    s := rebuildOrderHeap s
    return { s with simpDBAssigns := s.trail.size,
                    simpDBProps := s.clausesLiterals + s.learntsLiterals }
  return true

/-- The result of a search. -/
inductive Result where
  | sat
  | unsat
  | unknown
  deriving BEq, Inhabited, Repr

/-- `search`: until a model, a refutation, or `nofConflicts` conflicts (a
restart). -/
partial def search (nofConflicts : Nat) : m Result := do
  let mut conflictC := 0
  let mut checkType := CheckType.withTheory
  repeat
    let confl ← propagate checkType
    if confl != CRef.undef then
      upd fun s => { s with conflicts := s.conflicts + 1 }
      conflictC := conflictC + 1
      if (← st).decisionLevel == 0 then
        if confl != CRef.lazy then finalizeExplain (← st).clauses[confl]!.lits
        return .unsat
      let confl ← if confl == CRef.lazy then pure confl else pure confl
      let (learnt, bt) ← analyze confl
      cancelUntil bt
      if learnt.size == 1 then
        uncheckedEnqueue learnt[0]!
        TheoryProxy.notifySatClause learnt
      else
        let cr ← modifyGetThe Solver fun s =>
          let (cr, s) := alloc s learnt true
          (cr, s)
        TheoryProxy.notifySatClause learnt
        upd fun s => claBumpActivity (attachClause { s with clausesRemovable := s.clausesRemovable.push cr } cr) cr
        uncheckedEnqueue learnt[0]! cr
      upd fun s => { s with varInc := s.varInc * (1 / s.varDecay),
                            claInc := s.claInc * (1 / s.clauseDecay) }
      upd fun s =>
        let cnt := s.learntsizeAdjustCnt - 1
        if cnt == 0 then
          let confl := s.learntsizeAdjustConfl * s.learntsizeAdjustInc
          { s with learntsizeAdjustConfl := confl, learntsizeAdjustCnt := confl.toUInt64.toNat,
                   maxLearnts := s.maxLearnts * s.learntsizeInc }
        else { s with learntsizeAdjustCnt := cnt }
      checkType := .withTheory
    else
      if checkType == .final then
        let done ← TheoryProxy.isDecisionEngineDone
        let s ← st
        if !done && (!s.orderHeap.empty || s.qhead < s.trail.size) then
          checkType := .withTheory
          continue
        else if s.recheck then continue
        else return .sat
      if conflictC ≥ nofConflicts then
        cancelUntil 0
        TheoryProxy.notifyRestart
        return .unknown
      -- (not `&&`: the nested action would run at every level)
      if (← st).decisionLevel == 0 then
        if !(← simplify) then return .unsat
      let s ← st
      if s.clausesRemovable.size.toFloat - s.trail.size.toFloat ≥ s.maxLearnts then reduceDB
      let next ← pickBranchLit
      if next == Lit.undef then
        checkType := .final
        continue
      newDecisionLevel
      uncheckedEnqueue next
  return .unknown

/-- `luby`. -/
def luby (y : Float) (x : Nat) : Float := Id.run do
  let mut size := 1
  let mut seq := 0
  while size < x + 1 do
    seq := seq + 1
    size := 2 * size + 1
  let mut x := x
  while size - 1 != x do
    size := (size - 1) / 2
    seq := seq - 1
    x := x % size
  return y ^ seq.toFloat

/-- `solve_`: searches with Luby restarts. -/
partial def solve : m Result := do
  if !(← st).ok then return .unsat
  upd fun s =>
    let ml := s.clausesPersistent.size.toFloat * s.learntsizeFactor
    { s with maxLearnts := ml, learntsizeAdjustConfl := s.learntsizeAdjustStartConfl.toFloat,
             learntsizeAdjustCnt := s.learntsizeAdjustStartConfl, model := #[] }
  let wasBusy := (← st).busy
  upd fun s => { s with busy := true }
  let mut restarts := 0
  let mut status := Result.unknown
  while status == .unknown do
    let s ← st
    let base := luby s.restartInc restarts
    status ← search (base * s.restartFirst.toFloat).toUInt64.toNat
    restarts := restarts + 1
  if status == .sat then upd fun s => { s with model := s.assigns }
  else if status == .unsat then upd fun s => { s with ok := false }
  upd fun s => { s with busy := wasBusy }
  return status

/-- The initial solver: the variables `true` and `false`, assigned. -/
def init : m Unit := do
  let vt ← newVar true false false
  let vf ← newVar false false false
  uncheckedEnqueue (Lit.mk vt false)
  uncheckedEnqueue (Lit.mk vf true)

end Solver

end Telos.Sat
