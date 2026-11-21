import Std.Data.HashMap
import Telos.Core.Node.Key
import Telos.Core.PolyNorm

/-!
# The Diophantine equation solver

A port of cvc5's `DioSolver` (`src/theory/arith/linear/dio_solver.cpp`, Griggio,
JSAT 2012), with its linear forms (`DioLinearForm`, `normal_form.h`). It solves
the integer equations of the variables whose bounds are equal: an equation
whose gcd does not divide its constant has no integer solution, a conflict
(`processEquationsForConflict`); with the speculative equations of the
variables at a bound, such an equation gives a cut (`processEquationsForCut`).

Equations are solved for a variable of coefficient `±1` (`solveIndex`); when
there is none, a variable `x` of least coefficient `a` is decomposed with a
fresh integer variable (`decomposeIndex`). Each equation of the trail has its
proof: the combination of the input equations it is.

Its state is context dependent, as cvc5's (`CDList`s and `CDO`s): the lists
are truncated and the values restored at a pop (`Dio.Mark`).
-/

namespace Telos.Solver.Arith

/-- `DioLinearForm`: `c₁ v₁ + … + cₙ vₙ + k`, the terms strictly sorted by
variable id, with no zero coefficient. -/
structure LForm (α : Type) where
  terms : Array (Nat × α) := #[]
  const : α
  deriving Inhabited, BEq, Repr

namespace LForm

variable {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1] [BEq α] [Inhabited α]

def zero : LForm α := ⟨#[], 0⟩
def ofConst (c : α) : LForm α := ⟨#[], c⟩
def mkVar (v : Nat) : LForm α := ⟨#[(v, 1)], 0⟩
def isConstant (f : LForm α) : Bool := f.terms.isEmpty
def size (f : LForm α) : Nat := f.terms.size

def find? (f : LForm α) (v : Nat) : Option α := (f.terms.find? (·.1 == v)).map (·.2)
def coeff (f : LForm α) (v : Nat) : α := (f.find? v).getD 0

/-- `operator*`. -/
def scale (f : LForm α) (c : α) : LForm α :=
  if c == 0 then zero else if c == 1 then f else ⟨f.terms.map fun (v, a) => (v, a * c), f.const * c⟩

/-- `combine`: `q a + r b`, the terms merged in one pass. -/
def combine (q : α) (a : LForm α) (r : α) (b : LForm α) : LForm α := Id.run do
  if q == 0 then return b.scale r
  if r == 0 then return a.scale q
  let sa := fun (x : α) => if q == 1 then x else q * x
  let sb := fun (x : α) => if r == 1 then x else r * x
  let mut out : Array (Nat × α) := #[]
  let mut i := 0
  let mut j := 0
  while i < a.terms.size && j < b.terms.size do
    let (vi, ci) := a.terms[i]!
    let (vj, cj) := b.terms[j]!
    if vi < vj then
      out := out.push (vi, sa ci); i := i + 1
    else if vj < vi then
      out := out.push (vj, sb cj); j := j + 1
    else
      let c := sa ci + sb cj
      if !(c == 0) then out := out.push (vi, c)
      i := i + 1; j := j + 1
  while i < a.terms.size do
    out := out.push (a.terms[i]!.1, sa a.terms[i]!.2); i := i + 1
  while j < b.terms.size do
    out := out.push (b.terms[j]!.1, sb b.terms[j]!.2); j := j + 1
  return ⟨out, sa a.const + sb b.const⟩

/-- `mkForm`: the terms in any order, like terms summed. -/
def mkForm (terms : Array (Nat × α)) (c : α) : LForm α :=
  terms.foldl (fun f (v, a) => combine 1 f a (mkVar v)) (ofConst c)

end LForm

/-- The bit length of an integer (`Integer::length`; 1 for zero). -/
def intLength (x : Int) : Nat := x.natAbs.log2 + 1

/-- `Integer::extendedGcd` (GMP's `mpz_gcdext`): `g = gcd a b ≥ 0` and `s`, `t`
with `a s + b t = g`, normally `|s| < |b| / (2g)` and `|t| < |a| / (2g)`; if
`|a| = |b|`, then `s = 0` and `t = sgn b`; otherwise `s = sgn a` if `b = 0`
or `|b| = 2g`, and `t = sgn b` if `a = 0` or `|a| = 2g`. -/
def extendedGcd (a b : Int) : Int × Int × Int :=
  let g : Int := (Int.gcd a b : Nat)
  if a == 0 && b == 0 then (0, 0, 0)
  else if a.natAbs == b.natAbs then (g, 0, b.sign)
  else if b == 0 then (g, a.sign, 0)
  else if a == 0 then (g, 0, b.sign)
  else if b.natAbs == 2 * g.natAbs then
    let s := a.sign
    (g, s, (g - a * s) / b)
  else if a.natAbs == 2 * g.natAbs then
    let t := b.sign
    (g, (g - b * t) / a, t)
  else
    -- a solution by Euclid on `|a|`, `|b|`, then the one with `|s| < |b| / (2g)`
    let rec euclid (fuel : Nat) (r0 r1 s0 s1 : Int) : Int :=
      match fuel with
      | 0 => s0
      | f + 1 => if r1 == 0 then s0 else
        let q := r0 / r1
        euclid f r1 (r0 - q * r1) s1 (s0 - q * s1)
    let x := euclid (2 * (a.natAbs + b.natAbs) + 2) (a.natAbs : Int) (b.natAbs : Int) 1 0
    let s0 := x * a.sign
    let m : Int := (b.natAbs / g.natAbs : Nat)
    let s1 := s0 % m
    let s := if 2 * s1 > m then s1 - m else s1
    (g, s, (g - a * s) / b)

/-- `Integer::floorQR`: floor division. -/
def floorQR (a d : Int) : Int × Int := (a.fdiv d, a.fmod d)

namespace LForm

/-- `coefficientGcd`: of the coefficients (0 for a constant form). -/
def coefficientGcd (f : LForm Int) : Int := f.terms.foldl (fun d (_, c) => (Int.gcd d c : Int)) 0

/-- `gcdWithConstant`. -/
def gcdWithConstant (f : LForm Int) : Int := (Int.gcd f.coefficientGcd f.const : Int)

/-- `exactDivide`. -/
def exactDivide (f : LForm Int) (g : Int) : LForm Int :=
  if g == 1 then f else ⟨f.terms.map fun (v, c) => (v, c / g), f.const / g⟩

/-- `maxLength`. -/
def maxLength (f : LForm Int) : Nat := f.terms.foldl (fun m (_, c) => max m (intLength c)) (intLength f.const)

/-- `computeQR`: `f = div q + r`, by floor division of each coefficient. -/
def computeQR (f : LForm Int) (div : Int) : LForm Int × LForm Int := Id.run do
  let (q0, r0) := floorQR f.const div
  let mut q : LForm Int := ofConst q0
  let mut r : LForm Int := ofConst r0
  for (v, c) in f.terms do
    let (qc, rc) := floorQR c div
    if qc != 0 then q := { q with terms := q.terms.push (v, qc) }
    if rc != 0 then r := { r with terms := r.terms.push (v, rc) }
  return (q, r)

def toRat (f : LForm Int) : LForm Rat := ⟨f.terms.map fun (v, c) => (v, (c : Rat)), f.const⟩

end LForm

/-- An equation of the trail (`DioSolver::Constraint`): the form `= 0`, its
proof (a combination of the input equations, by index), and its term of
least absolute coefficient. -/
structure DioConstraint where
  eq : LForm Int
  proof : LForm Rat
  minTerm : Nat × Int
  deriving Inhabited

def DioConstraint.minAbs (c : DioConstraint) : Nat := c.minTerm.2.natAbs

/-- A substitution: the eliminated variable, by the equation (of coefficient
`-1` for it) at a trail index, and the fresh variable it introduced, if any. -/
structure DioSub where
  hasFresh : Bool
  fresh : Nat
  eliminated : Nat
  constraint : Nat
  deriving Inhabited

/-- What `Dio` restores at a pop. -/
structure DioMark where
  inputs : Nat
  nextInput : Nat
  trail : Nat
  subs : Nat
  savedQueue : Nat
  savedQueueIndex : Nat
  conflictIndex : Option Nat
  maxInputLength : Nat
  usedDecompose : Bool
  deriving Inhabited

/-- The solver's state. -/
structure Dio where
  /-- The variables (their nodes, cvc5's `VarList`s), by id, and their ids
  (not context dependent). -/
  varNodes : Array Node := #[]
  varIds : Std.HashMap Key Nat := {}
  /-- The input equations: their reasons, their positions in the trail, and
  the constraints of the reasons (for certificates). -/
  inputs : Array (Node × Nat × Array Nat) := #[]
  nextInput : Nat := 0
  trail : Array DioConstraint := #[]
  subs : Array DioSub := #[]
  /-- The queue of equations being processed (`d_currentF`). -/
  currentF : Array Nat := #[]
  savedQueue : Array Nat := #[]
  savedQueueIndex : Nat := 0
  conflictIndex : Option Nat := none
  maxInputLength : Nat := 0
  usedDecompose : Bool := false
  /-- The fresh variables made (`makeIntegerVariable`). -/
  freshCount : Nat := 0
  /-- The approximation of node ids (the arithmetic solver's `age`), which
  orders skolems as cvc5 does, by their creation. -/
  ages : Std.HashMap Key Nat := {}
  deriving Inhabited

namespace Dio

def mark (d : Dio) : DioMark :=
  ⟨d.inputs.size, d.nextInput, d.trail.size, d.subs.size, d.savedQueue.size, d.savedQueueIndex,
   d.conflictIndex, d.maxInputLength, d.usedDecompose⟩

def restore (d : Dio) (m : DioMark) : Dio :=
  { d with inputs := d.inputs.extract 0 m.inputs, nextInput := m.nextInput,
           trail := d.trail.extract 0 m.trail, subs := d.subs.extract 0 m.subs,
           savedQueue := d.savedQueue.extract 0 m.savedQueue, savedQueueIndex := m.savedQueueIndex,
           conflictIndex := m.conflictIndex, maxInputLength := m.maxInputLength,
           usedDecompose := m.usedDecompose }

abbrev DioM := StateM Dio

def varId (n : Node) : DioM Nat := do
  let d ← get
  match d.varIds.get? ⟨n⟩ with
  | some v => return v
  | none =>
    let v := d.varNodes.size
    set { d with varNodes := d.varNodes.push n, varIds := d.varIds.insert ⟨n⟩ v }
    return v

/-- `varListCmp`: cvc5's order of the variables (`VarList::cmp`): by node id
between two skolems (approximated by `ages`), as in the normal form
otherwise. -/
def varLt (d : Dio) (a b : Nat) : Bool :=
  let na := d.varNodes[a]!
  let nb := d.varNodes[b]!
  match na, nb with
  | .skolem .., .skolem .. =>
    match d.ages.get? ⟨na⟩, d.ages.get? ⟨nb⟩ with
    | some i, some j => i < j
    | _, _ => Telos.Arith.monoLt [na] [nb]
  | _, _ => Telos.Arith.monoLt [na] [nb]

/-- `minimalTerm`: the term of least absolute coefficient, ties going to the
least variable in cvc5's order. -/
def minimalTerm (d : Dio) (eq : LForm Int) : Nat × Int := Id.run do
  if eq.terms.isEmpty then return (0, 0)
  let mut best := 0
  for i in [1:eq.terms.size] do
    let a := eq.terms[i]!.2.natAbs
    let b := eq.terms[best]!.2.natAbs
    if a < b || (a == b && varLt d eq.terms[i]!.1 eq.terms[best]!.1) then best := i
  return eq.terms[best]!

def pushToTrail (eq : LForm Int) (proof : LForm Rat) : DioM Nat := do
  let d ← get
  set { d with trail := d.trail.push ⟨eq, proof, minimalTerm d eq⟩ }
  return d.trail.size

def inConflict (d : Dio) : Bool := d.conflictIndex.isSome

def raiseConflict (ti : Nat) : DioM Unit := modify fun d => { d with conflictIndex := some ti }

def triviallySat (d : Dio) (i : Nat) : Bool := let e := d.trail[i]!.eq; e.isConstant && e.const == 0
def triviallyUnsat (d : Dio) (i : Nat) : Bool := let e := d.trail[i]!.eq; e.isConstant && e.const != 0

/-- `pushInputConstraint`: an equation `f = 0` (integral, from a SumPair) and
its reason. The form is built from the monomials `(c, x)` in order, each new
variable getting the next id. -/
def pushInputConstraint (monos : Array (Int × Node)) (k : Int) (reason : Node) (cons : Array Nat := #[]) :
    DioM Unit := do
  let mut terms : Array (Nat × Int) := #[]
  for (c, x) in monos do terms := terms.push (← varId x, c)
  let f := LForm.mkForm terms k
  let len := f.maxLength
  modify fun d => { d with maxInputLength := max d.maxInputLength len }
  let d ← get
  let pos := d.inputs.size
  let posInTrail := d.trail.size
  let _ ← pushToTrail f (LForm.mkVar pos)
  modify fun d => { d with inputs := d.inputs.push (reason, posInTrail, cons) }

/-- `scaleEqAtIndex`: the equation divided by `g`. -/
def scaleEqAtIndex (i : Nat) (g : Int) : DioM Nat := do
  let c := (← get).trail[i]!
  pushToTrail (c.eq.exactDivide g) (c.proof.scale (1 / (g : Rat)))

/-- `combineEqAtIndexes`: `q eqᵢ + r eqⱼ`. -/
def combineEqAtIndexes (i : Nat) (q : Int) (j : Nat) (r : Int) : DioM Nat := do
  let d ← get
  let a := d.trail[i]!
  let b := d.trail[j]!
  pushToTrail (LForm.combine q a.eq r b.eq) (LForm.combine (q : Rat) a.proof (r : Rat) b.proof)

/-- `applySubstitution`. -/
def applySubstitution (si ti : Nat) : DioM Nat := do
  let d ← get
  let s := d.subs[si]!
  match d.trail[ti]!.eq.find? s.eliminated with
  | none => return ti
  | some a => combineEqAtIndexes ti 1 s.constraint a

def applyAllSubstitutionsToIndex (ti : Nat) : DioM Nat := do
  let mut cur := ti
  for si in [0:(← get).subs.size] do cur ← applySubstitution si cur
  return cur

/-- `reduceByGCD`: the equation divided by the gcd of its coefficients, or a
conflict if that does not divide the constant. -/
def reduceByGCD (ti : Nat) : DioM Nat := do
  let eq := (← get).trail[ti]!.eq
  let g := eq.coefficientGcd
  if eq.const % g == 0 then
    if g > 1 then scaleEqAtIndex ti g else return ti
  else
    raiseConflict ti
    return ti

def anyCoefficientExceedsMaximum (d : Dio) (j : Nat) : Bool :=
  let eq := d.trail[j]!.eq
  eq.size ≥ 2 && eq.maxLength > d.maxInputLength + 3  -- `MAX_GROWTH_RATE`

/-- `enqueueInputConstraints`: the saved queue, then the new input equations,
with the substitutions applied. -/
def enqueueInputConstraints : DioM Unit := do
  while (← get).savedQueueIndex < (← get).savedQueue.size do
    modify fun d => { d with currentF := d.currentF.push d.savedQueue[d.savedQueueIndex]!,
                             savedQueueIndex := d.savedQueueIndex + 1 }
  while (← get).nextInput < (← get).inputs.size && !inConflict (← get) do
    let curr := (← get).nextInput
    modify fun d => { d with nextInput := d.nextInput + 1 }
    let i := (← get).inputs[curr]!.2.1
    let j ← applyAllSubstitutionsToIndex i
    if !triviallySat (← get) j then
      if triviallyUnsat (← get) j then raiseConflict j
      else
        let k ← reduceByGCD j
        if !inConflict (← get) then
          if triviallyUnsat (← get) k then raiseConflict k
          else if !(triviallySat (← get) k || anyCoefficientExceedsMaximum (← get) k) then
            modify fun d => { d with currentF := d.currentF.push k }

/-- `moveMinimumByAbsToQueueFront`: the first equation of least `minAbs` is
swapped with the front. -/
def moveMinimumByAbsToQueueFront : DioM Unit := do
  let d ← get
  let mut idx := 0
  for i in [1:d.currentF.size] do
    if d.trail[d.currentF[i]!]!.minAbs < d.trail[d.currentF[idx]!]!.minAbs then idx := i
  let tmp := d.currentF[idx]!
  set { d with currentF := (d.currentF.set! idx d.currentF[0]!).set! 0 tmp }

/-- `columnGcdIsOne`: a variable whose coefficients in the queue have gcd 1
(each equation's terms visited in cvc5's variable order). -/
def columnGcdIsOne (d : Dio) : Option Nat := Id.run do
  let mut gcds : Std.HashMap Nat Int := {}
  for curr in d.currentF do
    let terms := d.trail[curr]!.eq.terms
    let order := (List.range terms.size).mergeSort fun a b => !varLt d terms[b]!.1 terms[a]!.1
    for k in order do
      let (v, c) := terms[k]!
      match gcds.get? v with
      | none => gcds := gcds.insert v c.natAbs
      | some g =>
        let ng : Int := (Int.gcd g c : Nat)
        if ng == 1 then return some v
        gcds := gcds.insert v ng
  return none

def saveQueue : DioM Unit := modify fun d => { d with savedQueue := d.savedQueue ++ d.currentF }

/-- `impliedGcdOfOne`: combine the queue's equations, by extended gcds, into
one whose coefficient of a variable is 1 (`0` if none). -/
def impliedGcdOfOne : DioM Nat := do
  let d ← get
  let some var := columnGcdIsOne d | return 0
  let mut i := 0
  let mut current := 0
  let mut currentCoeff : Int := 0
  let mut currentGcd : Int := 0
  -- the first equation with the variable
  while i < d.currentF.size do
    current := d.currentF[i]!
    i := i + 1
    if let some c := d.trail[current]!.eq.find? var then
      currentCoeff := c
      currentGcd := c.natAbs
      break
  while i < d.currentF.size do
    let inQueue := d.currentF[i]!
    i := i + 1
    if let some iqc := (← get).trail[inQueue]!.eq.find? var then
      let (g, s, t) := extendedGcd currentCoeff iqc
      if g < currentGcd then
        if s == 0 then
          current := inQueue
          currentCoeff := iqc
          currentGcd := iqc.natAbs
        else
          let next ← combineEqAtIndexes current s inQueue t
          current := next
          currentCoeff := g
          currentGcd := g
          if currentGcd == 1 then return current
  return 0

/-- `solveIndex`: solve the equation for its variable of coefficient `±1`
(scaled so that it is `-1`). -/
def solveIndex (i : Nat) : DioM (Nat × Nat) := do
  let (var, a) := (← get).trail[i]!.minTerm
  let ci ← if a > 0 then scaleEqAtIndex i (-1) else pure i
  let subBy := (← get).subs.size
  modify fun d => { d with subs := d.subs.push ⟨false, 0, var, ci⟩ }
  return (subBy, i)

/-- `decomposeIndex`: for the variable `x` of least coefficient `a` (`|a| > 1`),
`eq = a q + r` (floor division), a fresh `σ = q`, and `eq` becomes `r + a σ`. -/
def decomposeIndex (i : Nat) : DioM (Nat × Nat) := do
  modify fun d => { d with usedDecompose := true }
  let c := (← get).trail[i]!
  let (var, a) := c.minTerm
  let (q, r) := c.eq.computeQR a
  let n := (← get).freshCount
  modify fun d => { d with freshCount := n + 1 }
  -- a dummy skolem: after the other variables in cvc5's order (a later node id)
  let fresh ← varId (.var s!"~intvar_{n}" .integer)
  let freshOne : LForm Int := LForm.mkVar fresh
  let ci ← pushToTrail (LForm.combine 1 freshOne (-1) q) LForm.zero
  let nextIndex ← pushToTrail (LForm.combine 1 r a freshOne) c.proof
  let subBy := (← get).subs.size
  modify fun d => { d with subs := d.subs.push ⟨true, fresh, var, ci⟩ }
  return (subBy, nextIndex)

/-- `subAndReduceCurrentFByIndex`: the substitution applied to the queue. -/
def subAndReduceCurrentFByIndex (si : Nat) : DioM Unit := do
  let n := (← get).currentF.size
  let mut out : Array Nat := #[]
  let mut r := 0
  while r < n && !inConflict (← get) do
    let curr := (← get).currentF[r]!
    r := r + 1
    let next ← applySubstitution si curr
    if next == curr then out := out.push curr
    else if triviallyUnsat (← get) next then raiseConflict next
    else if !triviallySat (← get) next then
      let nn ← reduceByGCD next
      if !(inConflict (← get) || anyCoefficientExceedsMaximum (← get) nn) then out := out.push nn
  if !inConflict (← get) then
    -- (the unread rest is dropped with the queue, which is cleared after)
    modify fun d => { d with currentF := out }

/-- `processEquations`: whether there is a conflict. -/
def processEquations (allowDecomposition : Bool) : DioM Bool := do
  enqueueInputConstraints
  while !(← get).currentF.isEmpty && !inConflict (← get) do
    moveMinimumByAbsToQueueFront
    let d ← get
    let minimum := d.currentF[0]!
    let mut reduceIndex := minimum
    let mut p := (0, 0)
    if d.trail[minimum]!.minAbs == 1 then
      modify fun d => { d with currentF := d.currentF.extract 1 d.currentF.size }
      p ← solveIndex minimum
    else
      let implied ← impliedGcdOfOne
      if implied != 0 then
        p ← solveIndex implied
        reduceIndex := implied
      else if allowDecomposition then
        modify fun d => { d with currentF := d.currentF.extract 1 d.currentF.size }
        p ← decomposeIndex minimum
      else
        saveQueue
        break
    let (subIndex, next) := p
    subAndReduceCurrentFByIndex subIndex
    if next != reduceIndex then
      if triviallyUnsat (← get) next then raiseConflict next
      else if !triviallySat (← get) next then
        modify fun d => { d with currentF := d.currentF.push next }
  modify fun d => { d with currentF := #[] }
  return inConflict (← get)

/-- `proveIndex`: the reasons of the input equations the equation combines,
flattened (by input index). -/
def proveIndex (i : Nat) : DioM (Array Node) := do
  let d ← get
  let mut out := #[]
  for (inp, _) in d.trail[i]!.proof.terms do
    let r := d.inputs[inp]!.1
    match r with
    | .app (.kind .AND) cs => out := out ++ cs
    | _ => out := out.push r
  return out

/-- The polynomial of a form (its variables' nodes as monomials). -/
def toPoly (d : Dio) (f : LForm Int) : Telos.Arith.Poly :=
  (f.terms.toList.map fun (v, c) => ([d.varNodes[v]!], (c : Rat))) ++ (if f.const == 0 then [] else [([], (f.const : Rat))])

/-- The input equations a trail equation combines: their constraints, their
polynomials (`= 0`), and their coefficients. -/
def proofInputs (d : Dio) (i : Nat) : Array (Array Nat × Telos.Arith.Poly × Rat) :=
  d.trail[i]!.proof.terms.map fun (inp, mu) =>
    let (_, pos, cons) := d.inputs[inp]!
    (cons, toPoly d d.trail[pos]!.eq, mu)

/-- `processEquationsForConflict`: the reasons of a conflict, if any. -/
def processEquationsForConflict : DioM (Option (Array Node)) := do
  if ← processEquations true then return some (← proveIndex (← get).conflictIndex.get!)
  return none

/-- `purifyIndex`: the equation with the fresh variables substituted back (the
last substitution first). -/
def purifyIndex (i : Nat) : DioM (LForm Int) := do
  let d ← get
  let mut curr := d.trail[i]!.eq
  for k in (List.range d.subs.size).reverse do
    let s := d.subs[k]!
    if !s.hasFresh then continue
    if let some a := curr.find? s.fresh then
      curr := LForm.combine (-1) curr a d.trail[s.constraint]!.eq
  return curr

/-- `processEquationsForCut`: the plane (a form with a gcd greater than 1 that
does not divide its constant), or none. -/
def processEquationsForCut : DioM (Option (LForm Int)) := do
  if ← processEquations true then return some (← purifyIndex (← get).conflictIndex.get!)
  return none

end Dio

end Telos.Solver.Arith
