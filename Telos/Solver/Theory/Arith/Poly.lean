import Telos.Core.PolyNorm
import Telos.Solver.Theory.Arith.Basic

/-!
# Normal-form atoms

What the linear solver reads of a normal-form arithmetic atom, after cvc5's
`Comparison` and `Polynomial` (`src/theory/arith/linear/normal_form.cpp`): the
kind of comparison, the variable part normalized to a positive leading
coefficient (`normalizedVariablePart`), which keys the arith variable of the
atom, and the bound as a delta-rational (`normalizedDeltaRational`).

A polynomial is its monomials in order, each a coefficient and the monomial's
variable part (a variable, or a product for nonlinear terms); a constant
monomial has the variable part `1`. The node of a variable part
(`Poly.node`) is built here, in cvc5's normal form, so that it keys the same
arith variable whichever atom it comes from.
-/

namespace Telos.Solver.Arith



/-- The value of a constant node. -/
def constVal? : Node → Option Rat
  | .const (.integer i) => some i
  | .const (.rational q) => some q
  | _ => none

/-- A polynomial in normal form: its monomials in order. -/
structure Poly where
  terms : Array (Rat × Node) := #[]
  deriving Inhabited, BEq

namespace Poly

/-- The constant monomial's variable part. -/
def one : Node := .const (.integer 1)

/-- `rewriter::removeToReal`. cvc5's normal forms mix integers and reals in sums;
telos's keep the `to_real` that Logos's typing needs, and the solver reads them
without it, so that `(to_real n)` is the arith variable of `n`. -/
def removeToReal : Node → Node
  | .app (.kind .TO_REAL) #[a] => a
  | n => n

/-- A monomial (`(* c m)`, or `m`, or a constant). -/
def monoOf (n : Node) : Rat × Node :=
  let n := removeToReal n
  match constVal? n with
  | some c => (c, one)
  | none =>
    match n with
    | .app (.kind .MULT) cs =>
      match cs[0]?.bind constVal? with
      | some c => (c, if cs.size == 2 then removeToReal cs[1]! else .app (.kind .MULT) (cs.extract 1 cs.size))
      | none => (1, n)
    | _ => (1, n)

/-- `Polynomial::parsePolynomial`. -/
def parse (n : Node) : Poly :=
  match removeToReal n with
  | .app (.kind .ADD) cs => ⟨cs.map monoOf⟩
  | n => ⟨#[monoOf n]⟩

def isConstantMono (m : Rat × Node) : Bool := m.2 == one
/-- `isConstant`: a single constant monomial (or none). -/
def isConstant (p : Poly) : Bool := p.terms.all isConstantMono
def containsConstant (p : Poly) : Bool := p.terms.any isConstantMono
/-- The polynomial without its constant (`getTail`, the constant being first). -/
def noConstant (p : Poly) : Poly := ⟨p.terms.filter (!isConstantMono ·)⟩
def headCoeff (p : Poly) : Rat := (p.terms[0]?.map (·.1)).getD 0
def leadingCoefficientIsPositive (p : Poly) : Bool := p.headCoeff > 0
def neg (p : Poly) : Poly := ⟨p.terms.map fun (c, m) => (-c, m)⟩

/-- An integer variable part (all its factors integers). -/
def monoIsInt (m : Node) : Bool :=
  match m with
  | .app (.kind .MULT) cs => cs.all Telos.Arith.isInt
  | _ => Telos.Arith.isInt m

def allIntegralVariables (p : Poly) : Bool := p.terms.all fun (_, m) => m == one || monoIsInt m
/-- `isIntegral`: integral variables and coefficients. -/
def isIntegral (p : Poly) : Bool := p.terms.all fun (c, m) => (m == one || monoIsInt m) && c.den == 1

/-- `p - q` (`Polynomial::operator-`), the monomials sorted as cvc5's sums
are (`Telos.Arith.Poly.sorted`). -/
def sub (p q : Poly) (o : NodeOrder := {}) : Poly :=
  let toPN (p : Poly) : Telos.Arith.Poly :=
    p.terms.foldl (fun acc (c, m) =>
      acc.addMono (if m == one then [] else match m with
        | .app (.kind .MULT) cs => cs.toList
        | m => [m]) c) []
  let d := (toPN p).add ((toPN q).scale (-1))
  ⟨(d.sorted o).toArray.map fun (mono, c) => (c, Telos.Arith.monoKey mono)⟩

/-- The node of a polynomial with no constant, in cvc5's normal form: a
monomial `m` with coefficient 1 is `m`, another is `(* c m)`; several are a
sum. An integer monomial of a real sum is cast, as in the rewriter's normal
form (`Telos.Arith.Poly.toNodeAt`). -/
def node (p : Poly) : Node :=
  let real := p.terms.any fun (c, m) => !monoIsInt m || c.den != 1
  let mono := fun (cm : Rat × Node) =>
    let (c, m) := cm
    if real && monoIsInt m then
      if c.den == 1 then
        Node.mkNode .TO_REAL #[if c == 1 then m else .app (.kind .MULT) #[Telos.Arith.constNode false c, m]]
      else .app (.kind .MULT) #[Telos.Arith.constNode true c, Node.mkNode .TO_REAL #[m]]
    else if c == 1 then m else .app (.kind .MULT) #[Telos.Arith.constNode real c, m]
  if h : p.terms.size = 1 then mono p.terms[0] else .app (.kind .ADD) (p.terms.map mono)

end Poly

/-- The kind of a comparison literal (`Comparison::comparisonKind`). -/
inductive CmpKind where
  | geq | gt | leq | lt | eq | distinct
  deriving BEq, Inhabited

/-- A comparison literal: its kind, and the children of its atom. -/
structure Comparison where
  kind : CmpKind
  left : Node
  right : Node
  deriving Inhabited

namespace Comparison

/-- `Comparison::parseNormalForm` of a literal. -/
def parse? (lit : Node) : Option Comparison :=
  match lit with
  | .app (.kind .GEQ) #[a, b] => some ⟨.geq, a, b⟩
  | .app (.kind .GT) #[a, b] => some ⟨.gt, a, b⟩
  | .app (.kind .EQUAL) #[a, b] => some ⟨.eq, a, b⟩
  | .app (.kind .NOT) #[.app (.kind .GEQ) #[a, b]] => some ⟨.lt, a, b⟩
  | .app (.kind .NOT) #[.app (.kind .GT) #[a, b]] => some ⟨.leq, a, b⟩
  | .app (.kind .NOT) #[.app (.kind .EQUAL) #[a, b]] => some ⟨.distinct, a, b⟩
  | _ => none

/-- `deltaCoeff`. -/
def deltaCoeff : CmpKind → Int
  | .lt => -1
  | .gt => 1
  | _ => 0

/-- `Constraint::constraintTypeOfComparison`. -/
def constraintType (c : Comparison) : CType :=
  let pos := (Poly.parse c.left).leadingCoefficientIsPositive
  match c.kind with
  | .lt | .leq => if pos then .upperBound else .lowerBound
  | .gt | .geq => if pos then .lowerBound else .upperBound
  | .eq => .equality
  | .distinct => .disequality

/-- `normalizedVariablePart`. -/
def normalizedVariablePart (c : Comparison) (o : NodeOrder := {}) : Poly :=
  match c.kind with
  | .lt | .leq | .gt | .geq =>
    let p := Poly.parse c.left
    if p.leadingCoefficientIsPositive then p else p.neg
  | .eq | .distinct =>
    let left := Poly.parse c.left
    let right := Poly.parse c.right
    if right.isConstant then left
    else
      let diff := left.sub right.noConstant o
      if diff.leadingCoefficientIsPositive then diff else diff.neg

/-- `normalizedDeltaRational`. -/
def normalizedDeltaRational (c : Comparison) (o : NodeOrder := {}) : DeltaRational :=
  let delta : Rat := (deltaCoeff c.kind : Rat)
  match c.kind with
  | .lt | .leq | .gt | .geq =>
    let q := (constVal? c.right).getD 0
    if (Poly.parse c.left).leadingCoefficientIsPositive then ⟨q, delta⟩ else ⟨-q, -delta⟩
  | .eq | .distinct =>
    let right := Poly.parse c.right
    match right.terms[0]? with
    | some (q, m) =>
      if m == Poly.one then
        let left := Poly.parse c.left
        if !left.allIntegralVariables then ⟨q, 0⟩
        else
          let diff := if right.terms.size == 1 then left else left.sub right.noConstant o
          if diff.leadingCoefficientIsPositive then ⟨q, 0⟩ else ⟨-q, 0⟩
      else 0
    | none => 0

end Comparison

end Telos.Solver.Arith
