import Telos.Core.Node.Key
import Telos.Solver.Theory.Arith.DeltaRational

/-!
# The arithmetic solver's basic types

From cvc5's `src/theory/arith/linear/`: bound counts (`bound_counts.h`), the
constraints (`constraint.h`) and the variables' information
(`partial_model.h`). A constraint is an index into the constraint database's
array (cvc5's `ConstraintP`), an arith variable a natural number (`ArithVar`).
-/

namespace Telos.Solver.Arith

/-- `BoundCounts`: numbers of lower and upper bounds. -/
structure BoundCounts where
  lb : Nat := 0
  ub : Nat := 0
  deriving BEq, Inhabited, Repr

namespace BoundCounts
instance : Add BoundCounts := ⟨fun a b => ⟨a.lb + b.lb, a.ub + b.ub⟩⟩
instance : Sub BoundCounts := ⟨fun a b => ⟨a.lb - b.lb, a.ub - b.ub⟩⟩
def isZero (b : BoundCounts) : Bool := b.lb == 0 && b.ub == 0
/-- `multiplyBySgn`: a negative sign swaps the counts. -/
def multiplyBySgn (b : BoundCounts) (sgn : Int) : BoundCounts :=
  if sgn > 0 then b else if sgn == 0 then {} else ⟨b.ub, b.lb⟩
/-- `addInChange`. -/
def addInChange (b : BoundCounts) (sgn : Int) (before after : BoundCounts) : BoundCounts :=
  if before == after then b
  else if sgn < 0 then ⟨b.lb + after.ub - before.ub, b.ub + after.lb - before.lb⟩
  else if sgn > 0 then ⟨b.lb + after.lb - before.lb, b.ub + after.ub - before.ub⟩
  else b
/-- `addInSgn`. -/
def addInSgn (b bc : BoundCounts) (before after : Int) : BoundCounts :=
  let b := if before < 0 then ⟨b.lb - bc.ub, b.ub - bc.lb⟩
    else if before > 0 then ⟨b.lb - bc.lb, b.ub - bc.ub⟩ else b
  if after < 0 then ⟨b.lb + bc.ub, b.ub + bc.lb⟩
  else if after > 0 then ⟨b.lb + bc.lb, b.ub + bc.ub⟩ else b
end BoundCounts

/-- `BoundsInfo`: the bounds a variable is at, and those it has. -/
structure BoundsInfo where
  atBounds : BoundCounts := {}
  hasBounds : BoundCounts := {}
  deriving BEq, Inhabited, Repr

namespace BoundsInfo
instance : Add BoundsInfo := ⟨fun a b => ⟨a.atBounds + b.atBounds, a.hasBounds + b.hasBounds⟩⟩
instance : Sub BoundsInfo := ⟨fun a b => ⟨a.atBounds - b.atBounds, a.hasBounds - b.hasBounds⟩⟩
def multiplyBySgn (b : BoundsInfo) (sgn : Int) : BoundsInfo :=
  ⟨b.atBounds.multiplyBySgn sgn, b.hasBounds.multiplyBySgn sgn⟩
def addInChange (b : BoundsInfo) (sgn : Int) (before after : BoundsInfo) : BoundsInfo :=
  ⟨b.atBounds.addInChange sgn before.atBounds after.atBounds,
   b.hasBounds.addInChange sgn before.hasBounds after.hasBounds⟩
def addInSgn (b bc : BoundsInfo) (before after : Int) : BoundsInfo :=
  ⟨b.atBounds.addInSgn bc.atBounds before after, b.hasBounds.addInSgn bc.hasBounds before after⟩
end BoundsInfo

/-- `ConstraintType`. -/
inductive CType where
  | lowerBound | equality | upperBound | disequality
  deriving BEq, Inhabited, Repr

/-- `ArithProofType`. -/
inductive ProofType where
  | assume | internalAssume | farkas | trichotomy | equalityEngine | intTighten | intHole
  deriving BEq, Inhabited, Repr

/-- A constraint (cvc5's `Constraint`): `x ⋈ v` for an arith variable `x`. Its
context-dependent fields are undone by the database's watches. -/
structure Constraint where
  var : Nat
  type : CType
  value : DeltaRational
  /-- `d_negation`. -/
  negation : Nat := 0
  /-- `d_literal`, the first literal attached. -/
  literal : Option Node := none
  /-- `d_canBePropagated` (context dependent). -/
  canBePropagated : Bool := false
  /-- `d_assertionOrder` and `d_witness` (context dependent). -/
  assertionOrder : Option Nat := none
  witness : Option Node := none
  /-- `d_crid`: its rule in the database's proofs (context dependent). -/
  crid : Option Nat := none
  /-- `d_split` (user-context dependent). -/
  split : Bool := false
  deriving Inhabited

namespace Constraint
def isEquality (c : Constraint) : Bool := c.type == .equality
def isDisequality (c : Constraint) : Bool := c.type == .disequality
def isLowerBound (c : Constraint) : Bool := c.type == .lowerBound
def isUpperBound (c : Constraint) : Bool := c.type == .upperBound
def isStrictUpperBound (c : Constraint) : Bool := c.value.infinitesimalSgn < 0
def isStrictLowerBound (c : Constraint) : Bool := c.value.infinitesimalSgn > 0
def hasProof (c : Constraint) : Bool := c.crid.isSome
def assertedToTheTheory (c : Constraint) : Bool := c.assertionOrder.isSome
def assertedBefore (c : Constraint) (t : Nat) : Bool := match c.assertionOrder with
  | some o => o < t
  | none => false
/-- `satisfiedBy`. -/
def satisfiedBy (c : Constraint) (d : DeltaRational) : Bool :=
  match c.type with
  | .lowerBound => c.value ≤ d
  | .equality => d == c.value
  | .upperBound => d ≤ c.value
  | .disequality => d != c.value
end Constraint

/-- `ValueCollection`: the constraints of one variable at one value. -/
structure ValueCollection where
  lb : Option Nat := none
  ub : Option Nat := none
  eq : Option Nat := none
  diseq : Option Nat := none
  deriving Inhabited, BEq

namespace ValueCollection
def get (vc : ValueCollection) : CType → Option Nat
  | .lowerBound => vc.lb
  | .upperBound => vc.ub
  | .equality => vc.eq
  | .disequality => vc.diseq
def set (vc : ValueCollection) (t : CType) (c : Option Nat) : ValueCollection :=
  match t with
  | .lowerBound => { vc with lb := c }
  | .upperBound => { vc with ub := c }
  | .equality => { vc with eq := c }
  | .disequality => { vc with diseq := c }
/-- `nonNull`. -/
def nonNull (vc : ValueCollection) : Option Nat := vc.lb <|> vc.ub <|> vc.eq <|> vc.diseq
end ValueCollection

/-- `ConstraintRule`: how a constraint was proven. `antecedentEnd` indexes the
database's antecedent list, whose lists end (going backward) at a `none`. -/
structure ConstraintRule where
  constraint : Nat
  proofType : ProofType
  antecedentEnd : Option Nat := none
  /-- The Farkas coefficients (entry 0 for the negation of the consequent). -/
  farkas : Option (Array Rat) := none
  deriving Inhabited

/-- The linear solver's options that the logic decides (`SetDefaults`,
`set_defaults.cpp`). -/
structure Options where
  /-- `arithHeuristicPivots`: 5, but 0 for pure quantifier-free real
  arithmetic, and -1 (the number of variables plus one) for difference logic. -/
  heuristicPivots : Int := 0
  /-- `arithPivotThreshold`: 2, but 16 for difference logic. -/
  pivotThreshold : Nat := 2
  /-- `arithStandardCheckVarOrderPivots`: 200 for pure quantifier-free
  arithmetic, -1 otherwise. -/
  varOrderPivots : Int := 200
  /-- `arithRewriteEq`: for pure linear quantifier-free arithmetic. -/
  rewriteEq : Bool := true
  deriving Inhabited, Repr

/-- The options of a logic: pure (arithmetic and no other theory),
quantified, linear, with integers, difference logic. -/
def Options.ofLogic (pure quantified linear integers difference : Bool) : Options :=
  let pureQF := pure && !quantified
  { heuristicPivots := if pureQF then (if difference then -1 else if !integers then 0 else 5) else 5
    pivotThreshold := if pureQF && difference then 16 else 2
    varOrderPivots := if pureQF then 200 else -1
    rewriteEq := pureQF && linear }

/-- `ArithType`. -/
inductive ArithType where
  | unset | real | integer
  deriving BEq, Inhabited

/-- `ArithVariables::VarInfo`. -/
structure VarInfo where
  initialized : Bool := false
  assignment : DeltaRational := 0
  lb : Option Nat := none
  ub : Option Nat := none
  cmpAssignmentLB : Int := 1
  cmpAssignmentUB : Int := -1
  pushCount : Nat := 0
  type : ArithType := .unset
  node : Node := default
  auxiliary : Bool := false
  deriving Inhabited

namespace VarInfo
def atBoundCounts (v : VarInfo) : BoundCounts :=
  ⟨if v.cmpAssignmentLB == 0 then 1 else 0, if v.cmpAssignmentUB == 0 then 1 else 0⟩
def hasBoundCounts (v : VarInfo) : BoundCounts :=
  ⟨if v.lb.isSome then 1 else 0, if v.ub.isSome then 1 else 0⟩
def boundsInfo (v : VarInfo) : BoundsInfo := ⟨v.atBoundCounts, v.hasBoundCounts⟩
end VarInfo

end Telos.Solver.Arith
