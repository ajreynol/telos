import Telos.Solver.Theory.Arith.State

/-!
# The dual simplex

Ports of cvc5's error set (`error_set.cpp`), linear equality module
(`linear_equality.cpp`), Farkas conflict builder (`callbacks.cpp`), and dual
simplex (`dual_simplex.cpp`, `simplex.cpp`), with the constraints' proof rules
(`Constraint::impliedBy*`, `constraint.cpp`).

The error set's focus is a heap in cvc5, whose order (the selection rule) is
total, so only its top matters: here it is a set, and the top is its least
element.
-/

namespace Telos.Solver.Arith

open State

/-! ## Proof rules of constraints -/

/-- Push an antecedent list (`d_antecedents`, a `none` then the antecedents);
the index of its last element. -/
def pushAntecedents (ants : Array Nat) : ArithM (Option Nat) := do
  modify fun s => { s with antecedents := (s.antecedents.push none) ++ ants.map some }
  return some ((← get).antecedents.size - 1)

/-- `unateFarkasSigns`. -/
def unateFarkasSigns (s : State) (ca cb : Nat) : Int × Int :=
  let a := s.constraint ca
  let b := s.constraint cb
  let sgnOf (t : CType) : Int := if t == .lowerBound then -1 else if t == .upperBound then 1 else 0
  let aS := sgnOf a.type
  let bS := sgnOf b.type
  if aS == 0 && bS == 0 then (if a.value < b.value then (1, -1) else (-1, 1))
  else if aS == 0 then (-bS, bS)
  else if bS == 0 then (aS, -aS)
  else (aS, bS)

/-- `impliedByUnate`. -/
def impliedByUnate (c imp : Nat) : ArithM Unit := do
  let e ← pushAntecedents #[imp]
  let s ← get
  let (f, g) := unateFarkasSigns s (s.constraint c).negation imp
  modify fun s => s.pushConstraintRule ⟨c, .farkas, e, some #[(f : Rat), (g : Rat)]⟩

/-- `impliedByTrichotomy`. -/
def impliedByTrichotomy (c a b : Nat) : ArithM Unit := do
  let e ← pushAntecedents #[a, b]
  modify fun s => s.pushConstraintRule ⟨c, .trichotomy, e, none⟩

/-- `impliedByIntTighten`. -/
def impliedByIntTighten (c a : Nat) : ArithM Unit := do
  let e ← pushAntecedents #[a]
  modify fun s => s.pushConstraintRule ⟨c, .intTighten, e, none⟩

/-- `impliedByFarkas`. -/
def impliedByFarkas (c : Nat) (ants : Array Nat) (coeffs : Array Rat) : ArithM Unit := do
  let e ← pushAntecedents ants
  modify fun s => s.pushConstraintRule ⟨c, .farkas, e, some coeffs⟩

/-- `TheoryArithPrivate::raiseConflict`. -/
def raiseConflict (c : Nat) (id : String) : ArithM Unit :=
  modify fun s => { s with conflicts := s.conflicts.push (c, id) }

/-! ## The error set -/

def inconsistent (s : State) (x : Nat) : Bool := !s.assignmentIsConsistent x
def inError (s : State) (x : Nat) : Bool := s.errInfo.isKey x
def signalVariable (x : Nat) : ArithM Unit := modify fun s => { s with signals := s.signals.push x }

/-- `computeDiff`: how far the assignment is from the violated bound. -/
def computeDiff (s : State) (v : Nat) : DeltaRational :=
  let beta := s.assignment v
  if (s.var v).cmpAssignmentLB < 0 then s.getLowerBound v - beta else beta - s.getUpperBound v

/-- `ComparatorPivotRule`: `v` comes before `u`. -/
def focusBefore (s : State) (v u : Nat) : Bool :=
  match s.selectionRule with
  | .varOrder => v < u
  | .minimumAmount =>
    let a := ((s.errInfo.get v).amount).getD 0
    let b := ((s.errInfo.get u).amount).getD 0
    let c := a.cmp b
    if c == 0 then v < u else c < 0

/-- `topFocusVariable`. -/
def topFocusVariable (s : State) : Option Nat :=
  s.focus.foldl (fun best v => match best with
    | none => some v
    | some b => if focusBefore s v b then some v else best) none

def setAmount (x : Nat) : ArithM Unit :=
  modify fun s => { s with errInfo := s.errInfo.modify x fun e => { e with amount := some (computeDiff s x) } }

/-- `setSelectionRule`: the amounts of the variables in focus are recomputed. -/
def setSelectionRule (r : SelectionRule) : ArithM Unit := do
  if r == (← get).selectionRule then return
  if r == .minimumAmount then
    for v in (← get).focus do
      if ((← get).errInfo.get v).inFocus then setAmount v
  modify fun s => { s with selectionRule := r }

def removeFromFocus (x : Nat) : ArithM Unit :=
  modify fun s => { s with focus := s.focus.filter (· != x) }

/-- `ErrorSet::update`. -/
def updateErr (x : Nat) : ArithM Unit := do
  if ((← get).errInfo.get x).inFocus && (← get).selectionRule == .minimumAmount then setAmount x

/-- `transitionVariableOutOfError`. -/
def transitionOutOfError (x : Nat) : ArithM Unit := do
  if ((← get).errInfo.get x).inFocus then removeFromFocus x
  modify fun s => { s with errInfo := s.errInfo.remove x }

/-- `transitionVariableIntoError`. -/
def transitionIntoError (x : Nat) : ArithM Unit := do
  let s ← get
  let vilb := (s.var x).cmpAssignmentLB < 0
  let c := if vilb then (s.var x).lb.get! else (s.var x).ub.get!
  modify fun s => { s with errInfo := s.errInfo.set x { var := x, violated := c, sgn := if vilb then 1 else -1 } }
  if (← get).selectionRule == .minimumAmount then setAmount x
  modify fun s => { s with errInfo := s.errInfo.modify x (fun e => { e with inFocus := true }),
                           focus := s.focus.push x }

/-- `popSignal`. -/
def popSignal : ArithM Int := do
  let s ← get
  let back := s.signals.back!
  modify fun s => { s with signals := s.signals.pop }
  if inError s back then
    let ei := s.errInfo.get back
    let focusSgn := if ei.inFocus then ei.sgn else 0
    let vilb := (s.var back).cmpAssignmentLB < 0
    let viub := (s.var back).cmpAssignmentUB > 0
    if vilb || viub then
      let currSgn : Int := if vilb then 1 else -1
      if currSgn != ei.sgn then
        let c := if vilb then (s.var back).lb.get! else (s.var back).ub.get!
        modify fun s => { s with errInfo := s.errInfo.modify back fun e =>
          { e with violated := c, sgn := currSgn, amount := none } }
      updateErr back
    else transitionOutOfError back
    return focusSgn
  else
    if inconsistent s back then transitionIntoError back
    return 0

/-- `reduceToSignals`: every variable in error becomes a signal. -/
def reduceToSignals : ArithM Unit := do
  for x in (← get).errInfo.keys do signalVariable x
  modify fun s => { s with errInfo := s.errInfo.purge, focus := #[], outOfFocus := #[] }

/-- `ErrorSet::clear`. -/
def clearErrorSet : ArithM Unit :=
  modify fun s => { s with signals := #[], errInfo := s.errInfo.purge, focus := #[] }

/-! ## The linear equality module -/

/-- `computeRowBoundInfo`. -/
def computeRowBoundInfo (s : State) (r : Nat) (inQueue : Bool) : BoundsInfo :=
  (s.tableau.rowEntries r).foldl (fun bi id =>
    let e := s.tableau.entry id
    let b := if inQueue && s.boundsQueue.isKey e.col then s.boundsQueue.get e.col else s.boundsInfo e.col
    bi + b.multiplyBySgn (ratSgn e.coeff)) {}

/-- `trackRowIndex`. -/
def trackRowIndex (r : Nat) : ArithM Unit :=
  modify fun s => { s with btracking := s.btracking.set r (computeRowBoundInfo s r true) }

/-- `includeBoundUpdate` (`UpdateTrackingCallback`): a change of a variable's
bound information is added to the counts of its rows. -/
def includeBoundUpdate (v : Nat) (prev : BoundsInfo) : ArithM Unit := do
  let s ← get
  let curr := s.boundsInfo v
  let mut bt := s.btracking
  for id in s.tableau.colEntries v do
    let e := s.tableau.entry id
    bt := bt.modify e.row fun bi => bi.addInChange (ratSgn e.coeff) prev curr
  modify fun s => { s with btracking := bt }

/-- `processBoundsQueue` with `UpdateTrackingCallback`. -/
def processBoundsQueueTracking : ArithM Unit := do
  let changed ← modifyGet fun s => let (s, out) := s.processBoundsQueue; (out, s)
  for (v, prev) in changed do includeBoundUpdate v prev

/-- `updateUntracked`: a nonbasic variable's new value, and its basic
variables'. -/
def updateUntracked (x : Nat) (v : DeltaRational) : ArithM Unit := do
  let diff := v - (← get).assignment x
  for id in (← get).tableau.colEntries x do
    let s ← get
    let e := s.tableau.entry id
    let xj := s.tableau.rowIndexToBasic e.row
    modify fun s => s.setAssignment xj (s.assignment xj + diff * e.coeff)
    signalVariable xj
  modify fun s => s.setAssignment x v

/-- `updateTracked`: as `updateUntracked`, the rows' bound counts kept. -/
def updateTracked (x : Nat) (v : DeltaRational) : ArithM Unit := do
  let s ← get
  let diff := v - s.assignment x
  let before := (s.var x).atBoundCounts
  modify fun s => s.setAssignment x v
  let after := ((← get).var x).atBoundCounts
  let anyChange := before != after
  for id in (← get).tableau.colEntries x do
    let s ← get
    let e := s.tableau.entry id
    let xj := s.tableau.rowIndexToBasic e.row
    let xjBefore := (s.var xj).atBoundCounts
    modify fun s => s.setAssignment xj (s.assignment xj + diff * e.coeff)
    let xjAfter := ((← get).var xj).atBoundCounts
    let sgn := ratSgn e.coeff
    modify fun s => { s with btracking := s.btracking.modify e.row fun bi =>
      let bi := if anyChange then { bi with atBounds := bi.atBounds.addInChange sgn before after } else bi
      if xjBefore != xjAfter then { bi with atBounds := bi.atBounds.addInChange (-1) xjBefore xjAfter } else bi }
    signalVariable xj

/-- `LinearEqualityModule::update`. -/
def update (x : Nat) (v : DeltaRational) : ArithM Unit := do
  if (← get).areTracking then updateTracked x v else updateUntracked x v

/-- The tracking callback of pivots (`TrackingCallback`), on the row counts,
given the variables' bound information. -/
def trackingCallback (s : State) : CoeffCallback (DenseMap BoundsInfo) where
  update bt r nb old new := bt.modify r fun bi => bi.addInSgn (s.boundsInfo nb) old new
  multiplyRow bt r sgn := if sgn < 0 then bt.modify r (·.multiplyBySgn sgn) else bt
  canUseRow bt r := bt.isKey r

/-- `pivotAndUpdate`: `x_j` replaces the basic `x_i`, whose new value is
`val`. -/
def pivotAndUpdate (xi xj : Nat) (val : DeltaRational) : ArithM Unit := do
  let s ← get
  let a := s.tableau.basicFindCoeff xi xj
  let theta := (val - s.assignment xi) / a
  updateTracked xj (s.assignment xj + theta)
  let s ← get
  let (t, bt) := s.tableau.pivot (trackingCallback s) s.btracking xi xj
  modify fun s => { s with tableau := t, btracking := bt }
  signalVariable xj

/-- `nonbasicsAtLowerBounds`. -/
def nonbasicsAtLowerBounds (s : State) (basic : Nat) : Bool :=
  let r := s.tableau.basicToRowIndex basic
  let lbc := (s.btracking.get r).atBounds.lb
  let len := s.tableau.rowLength r
  lbc == len || (lbc + 1 == len && (s.var basic).cmpAssignmentUB != 0)

/-- `nonbasicsAtUpperBounds`. -/
def nonbasicsAtUpperBounds (s : State) (basic : Nat) : Bool :=
  let r := s.tableau.basicToRowIndex basic
  let ubc := (s.btracking.get r).atBounds.ub
  let len := s.tableau.rowLength r
  ubc == len || (ubc + 1 == len && (s.var basic).cmpAssignmentLB != 0)

def hasEitherBound (s : State) (x : Nat) : Bool := (s.var x).lb.isSome || (s.var x).ub.isSome

/-- The entering-variable preferences (`VarPreferenceFunction`). -/
inductive Pref where
  | minVarOrder | minBoundAndColLength

def minColLength (s : State) (x y : Nat) : Nat :=
  let xl := s.tableau.colLength x
  let yl := s.tableau.colLength y
  if xl > yl then y else if xl == yl then min x y else x

def Pref.apply (s : State) : Pref → Nat → Nat → Nat
  | .minVarOrder, x, y => min x y
  | .minBoundAndColLength, x, y =>
    if hasEitherBound s x && !hasEitherBound s y then y
    else if !hasEitherBound s x && hasEitherBound s y then x
    else minColLength s x y

/-- `isAcceptableSlack`. -/
def isAcceptableSlack (s : State) (above : Bool) (sgn : Int) (nb : Nat) : Bool :=
  (above && sgn < 0 && s.strictlyBelowUpperBound nb) || (above && sgn > 0 && s.strictlyAboveLowerBound nb) ||
  (!above && sgn > 0 && s.strictlyBelowUpperBound nb) || (!above && sgn < 0 && s.strictlyAboveLowerBound nb)

/-- `selectSlack`: the preferred acceptable nonbasic variable of the row, folded
in the row's order. `above` is `selectSlackLowerBound` (the basic variable is
above its upper bound). -/
def selectSlack (s : State) (above : Bool) (xi : Nat) (pref : Pref) : Option Nat :=
  (s.tableau.basicRowEntries xi).foldl (fun slack id =>
    let e := s.tableau.entry id
    if e.col == xi || !isAcceptableSlack s above (ratSgn e.coeff) e.col then slack
    else match slack with
      | none => some e.col
      | some sl => some (pref.apply s sl e.col)) none

/-- `weakestExplanation`: the bound of `v` that explains the conflict, weakened
along the asserted bounds with literals while the surplus allows. -/
def weakestExplanation (s : State) (aboveUpper : Bool) (surplus : DeltaRational) (v : Nat) (coeff : Rat) :
    Nat × DeltaRational := Id.run do
  let sgn := ratSgn coeff
  let ub := if aboveUpper then sgn < 0 else sgn > 0
  let mut c := if ub then (s.var v).ub.get! else (s.var v).lb.get!
  let mut surplus := surplus
  repeat
    let bound := (s.constraint c).value
    let weaker := if ub then s.getStrictlyWeakerUpperBound c true true else s.getStrictlyWeakerLowerBound c true true
    match weaker with
    | some w =>
      let wb := (s.constraint w).value
      let diff := (if aboveUpper then bound - wb else wb - bound) * coeff
      if surplus > diff then
        surplus := surplus - diff
        c := w
      else break
    | none => break
  return (c, surplus)

/-- `minimallyWeakConflict`, with the Farkas conflict builder
(`FarkasConflictBuilder`): the constraints of the basic variable's row, the
basic variable's own bound the consequent; the conflict is its negation,
implied by Farkas. -/
def minimallyWeakConflict (aboveUpper : Bool) (basic : Nat) : ArithM Nat := do
  let s ← get
  let adjust : Rat := if aboveUpper then -1 else 1
  let mut surplus := if aboveUpper then s.assignment basic - s.getUpperBound basic
    else s.getLowerBound basic - s.assignment basic
  let mut consequent : Option Nat := none
  let mut constraints : Array Nat := #[]
  let mut farkas : Array Rat := #[]
  for id in s.tableau.basicRowEntries basic do
    let e := s.tableau.entry id
    let (c, sp) := weakestExplanation s aboveUpper surplus e.col e.coeff
    surplus := sp
    -- `addConstraint`
    if consequent.isNone then consequent := some c else constraints := constraints.push c
    farkas := farkas.push (e.coeff * adjust)
    -- `makeLastConsequent`
    if e.col == basic && !constraints.isEmpty then
      let last := constraints.back!
      constraints := constraints.set! (constraints.size - 1) consequent.get!
      consequent := some last
      let f0 := farkas[0]!
      farkas := (farkas.set! 0 farkas.back!).set! (farkas.size - 1) f0
  let notC := (s.constraint consequent.get!).negation
  impliedByFarkas notC constraints farkas
  return notC

/-! ## The dual simplex -/

/-- `checkBasicForConflict`. -/
def checkBasicForConflict (s : State) (basic : Nat) : Bool :=
  if (s.var basic).cmpAssignmentLB < 0 then nonbasicsAtUpperBounds s basic
  else if (s.var basic).cmpAssignmentUB > 0 then nonbasicsAtLowerBounds s basic
  else false

/-- `reportConflict`. -/
def reportConflict (basic : Nat) : ArithM Unit := do
  let s ← get
  let c ← minimallyWeakConflict ((s.var basic).cmpAssignmentLB ≥ 0) basic
  raiseConflict c "ARITH_CONF_SIMPLEX"
  modify fun s => { s with conflictVariables := s.conflictVariables.add basic }

/-- `standardProcessSignals`: the signals from the last; a conflict for each
inconsistent basic variable whose row cannot move it. -/
def processSignals : ArithM Bool := do
  while !(← get).signals.isEmpty do
    let s ← get
    let curr := s.signals.back!
    if s.tableau.isBasic curr && !s.assignmentIsConsistent curr then
      if !s.conflictVariables.isMember curr && checkBasicForConflict s curr then reportConflict curr
    let _ ← popSignal
  return !(← get).conflictVariables.isEmpty

/-- `searchForFeasibleSolution`: at most `n` pivots; whether a conflict was
found. -/
def searchForFeasibleSolution (n : Nat) : ArithM Bool := do
  let mut remaining := n
  while remaining > 0 && !(← get).focus.isEmpty do
    let s ← get
    let some xi := topFocusVariable s | return false
    remaining := remaining - 1
    let useVarOrder := s.pivotsInRound.count xi ≥ 2  -- `arithPivotThreshold`
    if !useVarOrder then modify fun s => { s with pivotsInRound := s.pivotsInRound.add xi }
    let pref := if useVarOrder then Pref.minVarOrder else .minBoundAndColLength
    let s ← get
    if (s.var xi).cmpAssignmentLB < 0 then
      if let some xj := selectSlack s false xi pref then pivotAndUpdate xi xj (s.getLowerBound xi)
    else if (s.var xi).cmpAssignmentUB > 0 then
      if let some xj := selectSlack s true xi pref then pivotAndUpdate xi xj (s.getUpperBound xi)
    let conflict ← processSignals
    modify fun s => { s with pivots := s.pivots + 1 }
    if conflict then return true
  return false

/-- `dualFindModel`. -/
def dualFindModel (exact : Bool) : ArithM Status := do
  modify fun s => { s with pivots := 0 }
  if (← get).errInfo.isEmpty && (← get).signals.isEmpty then return .sat
  reduceToSignals
  setSelectionRule .varOrder
  if ← processSignals then
    modify fun s => { s with conflictVariables := s.conflictVariables.purge }
    return .unsat
  if (← get).errInfo.isEmpty then return .sat
  let mut result := Status.unknown
  let limit := (← get).varOrderPivotLimit
  let exact := exact || limit < 0
  let nDiff := (← get).heuristicPivots
  if nDiff > 0 then
    setSelectionRule .minimumAmount
    if ← searchForFeasibleSolution nDiff then result := .unsat
  if !(← get).errInfo.isEmpty && result != .unsat then
    if exact then
      setSelectionRule .varOrder
      while !(← get).errInfo.isEmpty && result != .unsat do
        if ← searchForFeasibleSolution 200 then result := .unsat  -- `arithSimplexCheckPeriod`
    else if limit > 0 then
      setSelectionRule .varOrder
      if ← searchForFeasibleSolution limit.toNat then result := .unsat
  if result == .unknown && (← get).errInfo.isEmpty then result := .sat
  modify fun s => { s with pivotsInRound := s.pivotsInRound.purge, conflictVariables := s.conflictVariables.purge }
  return result

end Telos.Solver.Arith
