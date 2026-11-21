import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Solver.Theory.Arith.Matrix
import Telos.Solver.Theory.Arith.Poly
import Telos.Solver.LinCert
import Telos.Solver.Theory.Arith.Dio

/-!
# The state of the linear arithmetic solver

The state of cvc5's `TheoryArithPrivate` and its components as one structure:
the partial model (`ArithVariables`, `partial_model.cpp`), the tableau, and the
constraint database (`ConstraintDatabase`, `constraint.cpp`). Further fields
(the error set, the simplex's state) are added with the modules that use them.

**Context dependence.** cvc5's context-dependent lists (`CDList`, with their
cleanups) are arrays here; a push saves their sizes (`Mark`), and a pop
truncates them, running the cleanups from the last element down, as
`CDList::truncateList` does:
- the bound revert histories (`d_lbRevertHistory`, `d_ubRevertHistory`), whose
  cleanup restores the previous bound;
- the constraint database's watches: the proofs (`d_constraintProofs`, which
  clear the constraint's rule), the preregistration flags and the assertion
  order;
- the antecedent list.
The assignments, the tableau and the variables are not context dependent.

**Node ids.** Where cvc5 orders nodes by id (the disjuncts of a unate lemma,
`proveOr`), telos approximates the ids by the order in which nodes first
occur in the input, children first (`age`).
-/

namespace Telos.Solver.Arith

/-- The sizes of the context-dependent lists at a push. -/
structure Mark where
  lbRevert : Nat
  ubRevert : Nat
  proofs : Nat
  antecedents : Nat
  canBePropagated : Nat
  assertionOrder : Nat
  toPropagate : Nat
  conflicts : Nat
  learnedBounds : Nat
  diseqQueue : Nat
  constantIntegers : Nat
  dio : DioMark
  blackBox : Option (Node × Option LinCert)
  deriving Inhabited

/-- `ErrorInformation`: a variable that violates a bound. -/
structure ErrInfo where
  var : Nat := 0
  violated : Nat := 0
  sgn : Int := 0
  inFocus : Bool := false
  amount : Option DeltaRational := none
  deriving Inhabited

/-- `ErrorSelectionRule`. -/
inductive SelectionRule where
  | varOrder | minimumAmount
  deriving BEq, Inhabited

/-- `Result::Status` of the real relaxation. -/
inductive Status where
  | sat | unsat | unknown
  deriving BEq, Inhabited, Repr

/-- What the solver sends out. -/
inductive Output where
  /-- A lemma, with the certificate of its clause (refuting the negations of
  its literals), if any. -/
  | lemma (id : String) (lem : Node) (cert : Option LinCert := none)
  /-- A conflict, with its certificate, if any. -/
  | conflict (id : String) (exp : Node) (cert : Option LinCert := none)
  | propagate (lit : Node)
  /-- `Valuation::ensureLiteral`: the node gets a SAT literal now. -/
  | ensureLiteral (n : Node)
  /-- `preferPhase`: the SAT solver is to prefer the literal with a phase. -/
  | phase (n : Node) (pol : Bool)
  /-- The pop of a speculative scope (`context::Context::ScopedPush`), which
  prints a `pop` event. -/
  | scopePop
  deriving Inhabited

structure State where
  -- The partial model (`ArithVariables`)
  vars : Array VarInfo := #[]
  safeAssignment : DenseMap DeltaRational := {}
  nodeToVar : Std.HashMap Key Nat := {}
  boundsQueue : DenseMap BoundsInfo := {}
  enqueueingBoundCounts : Bool := true
  lbRevert : Array (Nat × Option Nat) := #[]
  ubRevert : Array (Nat × Option Nat) := #[]
  deltaIsSafe : Bool := false
  delta : Rat := -1
  -- The tableau
  tableau : Tableau := {}
  -- The constraint database
  constraints : Array Constraint := #[]
  /-- Each variable's constraints, sorted by value (`SortedConstraintMap`). -/
  scm : Array (Array (DeltaRational × ValueCollection)) := #[]
  nodeToConstraint : Std.HashMap Key Nat := {}
  proofs : Array ConstraintRule := #[]
  antecedents : Array (Option Nat) := #[]
  canBePropagatedW : Array Nat := #[]
  assertionOrderW : Array Nat := #[]
  /-- `d_toPropagate` (a context-dependent queue): from `toPropagateHead` on. -/
  toPropagate : Array Nat := #[]
  toPropagateHead : Nat := 0
  -- `TheoryArithPrivate`
  /-- `d_setupNodes` (`isSetup`, `markSetup`). -/
  setupNodes : Std.HashSet Key := {}
  /-- The approximation of node ids (see above). -/
  age : Std.HashMap Key Nat := {}
  marks : Array Mark := #[]
  outputs : Array Output := #[]
  /-- Why the solver cannot go on (a nonlinear term, say): the answer is then
  `unknown`. -/
  unsupported : Option String := none
  -- the error set (`ErrorSet`)
  errInfo : DenseMap ErrInfo := {}
  /-- The variables in focus (`d_focus`, a heap whose top is the least by the
  selection rule, a total order: a set suffices). -/
  focus : Array Nat := #[]
  outOfFocus : Array Nat := #[]
  signals : Array Nat := #[]
  selectionRule : SelectionRule := .minimumAmount
  -- the linear equality module: the bound counts of the tracked rows
  btracking : DenseMap BoundsInfo := {}
  areTracking : Bool := false
  -- the dual simplex
  pivotsInRound : DenseMultiset := {}
  conflictVariables : DenseSet := {}
  pivots : Nat := 0
  /-- The options that the logic decides. -/
  opts : Options := {}
  -- `TheoryArithPrivate`
  qflraStatus : Status := .unknown
  previousStatus : Status := .unknown
  newFacts : Bool := false
  /-- `d_conflicts` (context dependent): the constraints in conflict, with
  their inference ids. -/
  conflicts : Array (Nat × String) := #[]
  /-- `d_learnedBounds` (a context-dependent queue). -/
  learnedBounds : Array Nat := #[]
  learnedBoundsHead : Nat := 0
  /-- `d_constantIntegerVariables` (a context-dependent queue): the integer
  variables whose bounds became equal, for the Diophantine solver. -/
  constantIntegers : Array Nat := #[]
  constantIntegersHead : Nat := 0
  /-- `d_nextIntegerCheckVar`: where the round robin of branch and bound is. -/
  nextIntegerCheckVar : Nat := 0
  /-- `d_hasDoneWorkSinceCut` and `d_dioSolveResources`. -/
  hasDoneWorkSinceCut : Bool := false
  dioSolveResources : Int := 0
  /-- The Diophantine solver (`d_diosolver`). -/
  dio : Dio := {}
  /-- `d_blackBoxConflict` (context dependent): a conflict that is not a
  constraint's (the Diophantine solver's). -/
  blackBox : Option (Node × Option LinCert) := none
  /-- The lemmas sent, rewritten (the inference manager's `d_lemmasSent`, user
  context dependent). -/
  lemmasSent : Std.HashSet Key := {}
  /-- `d_diseqQueue` (a context-dependent queue). -/
  diseqQueue : Array Nat := #[]
  diseqQueueHead : Nat := 0
  /-- `d_currentPropagationList` (a deque, not context dependent). -/
  propList : Array (Option Nat) := #[]
  propListHead : Nat := 0
  /-- `d_updatedBounds`. -/
  updatedBounds : DenseSet := {}
  deriving Inhabited

abbrev ArithM := StateM State

namespace State

/-! ## Node ids -/

/-- Record the nodes of `n`, children first, that have no id yet. -/
partial def noteAges (s : State) (n : Node) : State :=
  if s.age.contains ⟨n⟩ then s else
  let s := match n with
    | .app _ cs => cs.foldl noteAges s
    | _ => s
  { s with age := s.age.insert ⟨n⟩ s.age.size }

/-- The id of a node (a new one if it has none). -/
def ageOf (n : Node) : ArithM Nat := do
  match (← get).age.get? ⟨n⟩ with
  | some a => return a
  | none => modifyGet fun s => (s.age.size, s.noteAges n)

/-! ## The partial model -/

def numVars (s : State) : Nat := s.vars.size
def var (s : State) (x : Nat) : VarInfo := s.vars[x]!
def assignment (s : State) (x : Nat) : DeltaRational := (s.var x).assignment
def lowerBound? (s : State) (x : Nat) : Option Nat := (s.var x).lb
def upperBound? (s : State) (x : Nat) : Option Nat := (s.var x).ub
def constraint (s : State) (c : Nat) : Constraint := s.constraints[c]!
def isInteger (s : State) (x : Nat) : Bool := (s.var x).type == .integer
def isAuxiliary (s : State) (x : Nat) : Bool := (s.var x).auxiliary
def hasArithVar (s : State) (n : Node) : Bool := s.nodeToVar.contains ⟨n⟩
def asArithVar? (s : State) (n : Node) : Option Nat := s.nodeToVar.get? ⟨n⟩
def asNode (s : State) (x : Nat) : Node := (s.var x).node

def getUpperBound (s : State) (x : Nat) : DeltaRational := (s.constraint (s.var x).ub.get!).value
def getLowerBound (s : State) (x : Nat) : DeltaRational := (s.constraint (s.var x).lb.get!).value

/-- `cmpToLowerBound`. -/
def cmpToLowerBound (s : State) (x : Nat) (c : DeltaRational) : Int :=
  match (s.var x).lb with
  | none => 1
  | some lb => c.cmp (s.constraint lb).value

/-- `cmpToUpperBound`. -/
def cmpToUpperBound (s : State) (x : Nat) (c : DeltaRational) : Int :=
  match (s.var x).ub with
  | none => -1
  | some ub => c.cmp (s.constraint ub).value

def assignmentIsConsistent (s : State) (x : Nat) : Bool :=
  let v := s.var x; v.cmpAssignmentLB ≥ 0 && v.cmpAssignmentUB ≤ 0
def strictlyBelowUpperBound (s : State) (x : Nat) : Bool := (s.var x).cmpAssignmentUB < 0
def strictlyAboveLowerBound (s : State) (x : Nat) : Bool := (s.var x).cmpAssignmentLB > 0
def boundsInfo (s : State) (x : Nat) : BoundsInfo := (s.var x).boundsInfo

/-- `addToBoundQueue`. -/
def addToBoundQueue (s : State) (v : Nat) (prev : BoundsInfo) : State :=
  if s.enqueueingBoundCounts && !s.boundsQueue.isKey v then { s with boundsQueue := s.boundsQueue.set v prev }
  else s

/-- `VarInfo::setAssignment`, and the bound queue. -/
def setVarAssignment (s : State) (x : Nat) (a : DeltaRational) : State :=
  let vi := s.var x
  let cmpUB := match vi.ub with
    | none => -1
    | some ub => a.cmp (s.constraint ub).value
  let cmpLB := match vi.lb with
    | none => 1
    | some lb => a.cmp (s.constraint lb).value
  let lbChanged := cmpLB != vi.cmpAssignmentLB && (cmpLB == 0 || vi.cmpAssignmentLB == 0)
  let ubChanged := cmpUB != vi.cmpAssignmentUB && (cmpUB == 0 || vi.cmpAssignmentUB == 0)
  let prev := vi.boundsInfo
  let s := { s with vars := s.vars.set! x { vi with assignment := a, cmpAssignmentUB := cmpUB,
                                                    cmpAssignmentLB := cmpLB } }
  if lbChanged || ubChanged then s.addToBoundQueue x prev else s

/-- `ArithVariables::setAssignment(x, r)`: an assignment not known to be consistent (the safe one is kept). -/
def setAssignment (s : State) (x : Nat) (r : DeltaRational) : State :=
  let s := if s.safeAssignment.isKey x then s
    else { s with safeAssignment := s.safeAssignment.set x (s.assignment x) }
  { s with deltaIsSafe := false }.setVarAssignment x r

/-- `ArithVariables::setAssignment(x, safe, r)`. -/
def setAssignment2 (s : State) (x : Nat) (safe r : DeltaRational) : State :=
  let s := if safe == r then { s with safeAssignment := s.safeAssignment.remove x }
    else { s with safeAssignment := s.safeAssignment.set x safe }
  { s with deltaIsSafe := false }.setVarAssignment x r

/-- `getSafeAssignment`. -/
def getSafeAssignment (s : State) (x : Nat) : DeltaRational :=
  (s.safeAssignment.get? x).getD (s.assignment x)

def getAssignmentSafe (s : State) (x : Nat) (safe : Bool) : DeltaRational :=
  if safe then s.getSafeAssignment x else s.assignment x

/-- `clearSafeAssignments`: revert to the safe assignments, or commit. -/
def clearSafeAssignments (s : State) (revert : Bool) : State := Id.run do
  let mut s := if revert && !s.safeAssignment.isEmpty then { s with deltaIsSafe := false } else s
  while !s.safeAssignment.isEmpty do
    let x := s.safeAssignment.back
    if revert then s := s.setVarAssignment x (s.safeAssignment.get x)
    s := { s with safeAssignment := s.safeAssignment.popBack }
  return s

def revertAssignmentChanges (s : State) : State := s.clearSafeAssignments true
def commitAssignmentChanges (s : State) : State := s.clearSafeAssignments false

/-- `VarInfo::setLowerBound`, and the bound queue. -/
def setVarLowerBound (s : State) (x : Nat) (lb : Option Nat) : State :=
  let vi := s.var x
  let cmpLB := match lb with
    | none => 1
    | some c => vi.assignment.cmp (s.constraint c).value
  let changed := vi.lb.isNone != lb.isNone ||
    (cmpLB != vi.cmpAssignmentLB && (cmpLB == 0 || vi.cmpAssignmentLB == 0))
  let prev := vi.boundsInfo
  let s := { s with vars := s.vars.set! x { vi with lb, cmpAssignmentLB := cmpLB } }
  if changed then s.addToBoundQueue x prev else s

/-- `VarInfo::setUpperBound`, and the bound queue. -/
def setVarUpperBound (s : State) (x : Nat) (ub : Option Nat) : State :=
  let vi := s.var x
  let cmpUB := match ub with
    | none => -1
    | some c => vi.assignment.cmp (s.constraint c).value
  let changed := vi.ub.isNone != ub.isNone ||
    (cmpUB != vi.cmpAssignmentUB && (cmpUB == 0 || vi.cmpAssignmentUB == 0))
  let prev := vi.boundsInfo
  let s := { s with vars := s.vars.set! x { vi with ub, cmpAssignmentUB := cmpUB } }
  if changed then s.addToBoundQueue x prev else s

/-- `setLowerBoundConstraint`: the previous bound goes on the revert history. -/
def setLowerBoundConstraint (s : State) (c : Nat) : State :=
  let x := (s.constraint c).var
  let vi := s.var x
  let s := { s with deltaIsSafe := false, lbRevert := s.lbRevert.push (x, vi.lb),
                    vars := s.vars.set! x { vi with pushCount := vi.pushCount + 1 } }
  s.setVarLowerBound x (some c)

/-- `setUpperBoundConstraint`. -/
def setUpperBoundConstraint (s : State) (c : Nat) : State :=
  let x := (s.constraint c).var
  let vi := s.var x
  let s := { s with deltaIsSafe := false, ubRevert := s.ubRevert.push (x, vi.ub),
                    vars := s.vars.set! x { vi with pushCount := vi.pushCount + 1 } }
  s.setVarUpperBound x (some c)

/-- `processBoundsQueue`: the variables whose bound information changed, with
the previous information, from the last queued. -/
def processBoundsQueue (s : State) : State × Array (Nat × BoundsInfo) := Id.run do
  let mut s := s
  let mut out := #[]
  while !s.boundsQueue.isEmpty do
    let v := s.boundsQueue.back
    let prev := s.boundsQueue.get v
    s := { s with boundsQueue := s.boundsQueue.popBack }
    if prev != s.boundsInfo v then out := out.push (v, prev)
  return (s, out)

/-- `allocate`: a new variable (no variable is ever released in the dual
simplex's configuration, so the numbering is sequential), its node mapped to
it. A slack's type is that of its polynomial. -/
def allocate (s : State) (n : Node) (aux : Bool) (integral : Bool) : State × Nat :=
  let x := s.vars.size
  let vi : VarInfo := { initialized := true, node := n, auxiliary := aux,
                        type := if integral then .integer else .real }
  ({ s with vars := s.vars.push vi, nodeToVar := s.nodeToVar.insert ⟨n⟩ x }, x)

/-! ## The constraint database -/

/-- The position of the value `v` in variable `x`'s sorted map, or where it
would be inserted. -/
def scmFind (m : Array (DeltaRational × ValueCollection)) (v : DeltaRational) : Nat × Bool := Id.run do
  let mut lo := 0
  let mut hi := m.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let c := m[mid]!.1.cmp v
    if c == 0 then return (mid, true)
    if c < 0 then lo := mid + 1 else hi := mid
  return (lo, false)

/-- The value collection of `x` at `v`, inserted if missing; its position. -/
def scmEnsure (s : State) (x : Nat) (v : DeltaRational) : State × Nat :=
  let m := s.scm[x]!
  let (i, found) := scmFind m v
  if found then (s, i) else ({ s with scm := s.scm.set! x (m.insertIdx! i (v, {})) }, i)

def scmAt (s : State) (x : Nat) (v : DeltaRational) : Option ValueCollection :=
  let m := s.scm[x]!
  let (i, found) := scmFind m v
  if found then some m[i]!.2 else none

def scmModify (s : State) (x : Nat) (v : DeltaRational) (f : ValueCollection → ValueCollection) : State :=
  let (s, i) := s.scmEnsure x v
  { s with scm := s.scm.modify x fun m => m.modify i fun (k, vc) => (k, f vc) }

/-- `addVariable`. -/
def addVariableDb (s : State) : State := { s with scm := s.scm.push #[] }

/-- `Constraint::makeNegation`'s type and value. -/
def negationOf (t : CType) (r : DeltaRational) : CType × DeltaRational :=
  match t with
  | .lowerBound => (.upperBound, if r.infinitesimalSgn > 0 then ⟨r.c, 0⟩ else ⟨r.c, -1⟩)
  | .upperBound => (.lowerBound, if r.infinitesimalSgn < 0 then ⟨r.c, 0⟩ else ⟨r.c, 1⟩)
  | .equality => (.disequality, r)
  | .disequality => (.equality, r)

/-- A new constraint and its negation, in their value collections. -/
private def newPair (s : State) (x : Nat) (t : CType) (r : DeltaRational) (nt : CType)
    (nr : DeltaRational) : State × Nat :=
  let c := s.constraints.size
  let s := { s with constraints := (s.constraints.push { var := x, type := t, value := r, negation := c + 1 }).push
                                     { var := x, type := nt, value := nr, negation := c } }
  let s := s.scmModify x r (·.set t (some c))
  let s := s.scmModify x nr (·.set nt (some (c + 1)))
  (s, c)

/-- `getConstraint`: the constraint of type `t` and value `r` on `x`, created
(with its negation) if missing. -/
def getConstraint (s : State) (x : Nat) (t : CType) (r : DeltaRational) : State × Nat :=
  match (s.scmAt x r).bind (·.get t) with
  | some c => (s, c)
  | none => let (nt, nr) := negationOf t r; newPair s x t r nt nr

/-- `setLiteral`: the first literal of a constraint is its literal; later
ones only map to it. -/
def setLiteral (s : State) (c : Nat) (n : Node) : State :=
  let s := { s with nodeToConstraint := s.nodeToConstraint.insert ⟨n⟩ c }
  if (s.constraint c).literal.isSome then s
  else { s with constraints := s.constraints.modify c fun k => { k with literal := some n } }

def lookup (s : State) (lit : Node) : Option Nat := s.nodeToConstraint.get? ⟨lit⟩

/-- `addLiteral`: the constraint of the literal `lit`, whose atom has the
normal form `nlit`; its negation gets the negated literal. -/
def addLiteral (s : State) (lit nlit : Node) : State × Nat :=
  let (isNot, atom) := match lit with
    | .app (.kind .NOT) #[a] => (true, a)
    | a => (false, a)
  let nAtom := match nlit with
    | .app (.kind .NOT) #[a] => a
    | a => a
  let negNode := Node.notNode atom
  let posCmp := (Comparison.parse? nAtom).get!
  let posType := posCmp.constraintType
  let x := (s.asArithVar? (posCmp.normalizedVariablePart s.opts.order).node).get!
  let posDR := posCmp.normalizedDeltaRational s.opts.order
  match (s.scmAt x posDR).bind (·.get posType) with
  | some hit =>
    let s := s.setLiteral hit atom
    let s := s.setLiteral (s.constraint hit).negation negNode
    (s, if isNot then (s.constraint hit).negation else hit)
  | none =>
    let negCmp := (Comparison.parse? (Node.notNode nAtom)).get!
    let (s, c) := newPair s x posType posDR negCmp.constraintType (negCmp.normalizedDeltaRational s.opts.order)
    let s := (s.setLiteral c atom).setLiteral (c + 1) negNode
    (s, if isNot then c + 1 else c)

/-- `pushCanBePropagatedWatch` (`setCanBePropagated`). -/
def setCanBePropagated (s : State) (c : Nat) : State :=
  { s with constraints := s.constraints.modify c (fun k => { k with canBePropagated := true }),
           canBePropagatedW := s.canBePropagatedW.push c }

/-- `setPreregistered`. -/
def setPreregistered (s : State) (c : Nat) : State :=
  let s := s.setCanBePropagated c
  s.setCanBePropagated (s.constraint c).negation

/-- `pushAssertionOrderWatch` (`setAssertedToTheTheory`). -/
def setAssertedToTheTheory (s : State) (c : Nat) (witness : Node) : State :=
  { s with constraints := s.constraints.modify c (fun k =>
             { k with assertionOrder := some s.assertionOrderW.size, witness := some witness }),
           assertionOrderW := s.assertionOrderW.push c }

/-- `pushConstraintRule`. -/
def pushConstraintRule (s : State) (r : ConstraintRule) : State :=
  { s with constraints := s.constraints.modify r.constraint (fun k => { k with crid := some s.proofs.size }),
           proofs := s.proofs.push r }

def rule (s : State) (c : Nat) : Option ConstraintRule := (s.constraint c).crid.map (s.proofs[·]!)
def proofType? (s : State) (c : Nat) : Option ProofType := (s.rule c).map (·.proofType)
def hasProof (s : State) (c : Nat) : Bool := (s.constraint c).hasProof
def negationHasProof (s : State) (c : Nat) : Bool := s.hasProof (s.constraint c).negation
def isTrue (s : State) (c : Nat) : Bool := s.hasProof c
def inConflict (s : State) (c : Nat) : Bool := s.hasProof c && s.negationHasProof c
def isAssumption (s : State) (c : Nat) : Bool := s.proofType? c == some .assume
def isInternalAssumption (s : State) (c : Nat) : Bool := s.proofType? c == some .internalAssume

/-- `setAssumption`. -/
def setAssumption (s : State) (c : Nat) : State := s.pushConstraintRule ⟨c, .assume, none, none⟩

/-- `propagate`: queue the constraint for the SAT solver. -/
def propagateC (s : State) (c : Nat) : State := { s with toPropagate := s.toPropagate.push c }

/-- `tryToPropagate`. -/
def tryToPropagate (s : State) (c : Nat) : State :=
  let k := s.constraint c
  if k.canBePropagated && !k.assertedToTheTheory && !s.isAssumption c && !s.isInternalAssumption c then
    s.propagateC c
  else s

/-- The position of a constraint in its variable's sorted map. -/
def scmPos (s : State) (c : Nat) : Nat :=
  let k := s.constraint c
  (scmFind s.scm[k.var]! k.value).1

/-- `getStrictlyWeakerLowerBound`: the nearest lower bound below. -/
def getStrictlyWeakerLowerBound (s : State) (c : Nat) (hasLiteral asserted : Bool) : Option Nat := Id.run do
  let k := s.constraint c
  let m := s.scm[k.var]!
  let mut i := s.scmPos c
  while i > 0 do
    i := i - 1
    if let some w := m[i]!.2.lb then
      let kw := s.constraint w
      if (!hasLiteral || kw.literal.isSome) && (!asserted || kw.assertedToTheTheory) then return some w
  return none

/-- `getStrictlyWeakerUpperBound`: the nearest upper bound above. -/
def getStrictlyWeakerUpperBound (s : State) (c : Nat) (hasLiteral asserted : Bool) : Option Nat := Id.run do
  let k := s.constraint c
  let m := s.scm[k.var]!
  for i in [s.scmPos c + 1:m.size] do
    if let some w := m[i]!.2.ub then
      let kw := s.constraint w
      if (!hasLiteral || kw.literal.isSome) && (!asserted || kw.assertedToTheTheory) then return some w
  return none

/-! ## Context -/

def push (s : State) : State :=
  { s with marks := s.marks.push ⟨s.lbRevert.size, s.ubRevert.size, s.proofs.size, s.antecedents.size,
                                   s.canBePropagatedW.size, s.assertionOrderW.size, s.toPropagate.size,
                                   s.conflicts.size, s.learnedBounds.size, s.diseqQueue.size,
                                   s.constantIntegers.size, s.dio.mark, s.blackBox⟩ }

/-- Pop one level: the lists back to their sizes at the push, with their
cleanups from the last element down. -/
def pop (s : State) : State := Id.run do
  let some m := s.marks.back? | return s
  let mut s := { s with marks := s.marks.pop }
  -- the bounds (`popLowerBound`, `popUpperBound`)
  while s.lbRevert.size > m.lbRevert do
    let (x, old) := s.lbRevert.back!
    s := { s with lbRevert := s.lbRevert.pop }
    s := s.setVarLowerBound x old
    s := { s with vars := s.vars.modify x fun v => { v with pushCount := v.pushCount - 1 } }
  while s.ubRevert.size > m.ubRevert do
    let (x, old) := s.ubRevert.back!
    s := { s with ubRevert := s.ubRevert.pop }
    s := s.setVarUpperBound x old
    s := { s with vars := s.vars.modify x fun v => { v with pushCount := v.pushCount - 1 } }
  -- the watches
  while s.proofs.size > m.proofs do
    let r := s.proofs.back!
    s := { s with proofs := s.proofs.pop,
                  constraints := s.constraints.modify r.constraint fun k => { k with crid := none } }
  while s.canBePropagatedW.size > m.canBePropagated do
    let c := s.canBePropagatedW.back!
    s := { s with canBePropagatedW := s.canBePropagatedW.pop,
                  constraints := s.constraints.modify c fun k => { k with canBePropagated := false } }
  while s.assertionOrderW.size > m.assertionOrder do
    let c := s.assertionOrderW.back!
    s := { s with assertionOrderW := s.assertionOrderW.pop,
                  constraints := s.constraints.modify c fun k => { k with assertionOrder := none, witness := none } }
  s := { s with antecedents := s.antecedents.extract 0 m.antecedents,
                toPropagate := s.toPropagate.extract 0 m.toPropagate,
                toPropagateHead := min s.toPropagateHead m.toPropagate,
                conflicts := s.conflicts.extract 0 m.conflicts,
                learnedBounds := s.learnedBounds.extract 0 m.learnedBounds,
                learnedBoundsHead := min s.learnedBoundsHead m.learnedBounds,
                diseqQueue := s.diseqQueue.extract 0 m.diseqQueue,
                diseqQueueHead := min s.diseqQueueHead m.diseqQueue,
                constantIntegers := s.constantIntegers.extract 0 m.constantIntegers,
                constantIntegersHead := min s.constantIntegersHead m.constantIntegers,
                dio := s.dio.restore m.dio, blackBox := m.blackBox }
  return s

end State

end Telos.Solver.Arith
