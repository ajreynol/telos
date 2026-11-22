import Cpc.Logos
import Telos.Core.Node.ToEo
import Telos.Core.Node.FastType
import Telos.Core.Node.Order
import Telos.Core.Node.NodeOrder
import Telos.Core.Node.DecEq
import Telos.Core.Profile

/-!
# Polynomial normal forms of arithmetic terms

cvc5's `rewriter::Sum` (`addition.cpp`): the polynomial of an arithmetic term
(`polyOf`) and the term of a polynomial in cvc5's normal form (`Poly.toNode`).
`arithNorm n` is the normal form of `n`.

This code is not trusted, and its results need no run-time check:
`verification/TelosProofs/Core/ArithNorm.lean` proves that `arithNorm n` has the
same polynomial value as `n`, so that CPC's `arith_poly_norm` accepts
`(= n (arithNorm n))` (given the conditions of `ArithNormOk`). It stays below
`Telos.Core.Certified` so that certified rewrites can name it.
-/

open Eo Smtm

namespace Telos.Arith

open Node

/-! ## Polynomials, as cvc5's `rewriter::Sum` -/

def isInt (n : Node) : Bool :=
  Profile.time "types" (fun _ => "arith: isInt/isReal") fun _ => n.typeHint == some .integer

def isReal (n : Node) : Bool :=
  Profile.time "types" (fun _ => "arith: isInt/isReal") fun _ => n.typeHint == some .real

/-- cvc5's `LeafNodeComparator`, for non-constant leaves: real terms before
integer terms, variables before other terms, then the term order. -/
def leafLt (a b : Node) : Bool :=
  if a == b then false
  else if isInt a != isInt b then !isInt a
  else if a.isVar != b.isVar then a.isVar
  else Node.lt a b

/-- A monomial: its non-constant factors, sorted by `leafLt`. -/
abbrev Mono := List Node

def sortLeaves (fs : List Node) : List Node :=
  fs.foldr (fun x acc => insert x acc) []
where
  insert (x : Node) : List Node → List Node
    | [] => [x]
    | y :: ys => if leafLt y x then y :: insert x ys else x :: y :: ys

/-- The node cvc5 keys a monomial by (`mkNonlinearMult`). -/
def monoKey : Mono → Node
  | [] => .const (.integer 1)
  | [x] => x
  | xs => mkNode .MULT xs.toArray

/-- cvc5's `LeafNodeComparator` on monomial keys: the constant monomial first,
then by node id (`o`, see `NodeOrder`). -/
def monoLt (a b : Mono) (o : NodeOrder := {}) : Bool :=
  match a, b with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | _, _ =>
    let ka := monoKey a
    let kb := monoKey b
    let ia := a.all isInt
    let ib := b.all isInt
    if ka == kb then false
    else if ia != ib then !ia
    else if ka.isVar != kb.isVar then ka.isVar
    else o.lt ka kb

/-- A sum of monomials with rational coefficients, none zero. -/
abbrev Poly := List (Mono × Rat)

namespace Poly

/-- Add `c` times the monomial `m`. Monomials are compared by `decide (_ = _)`
(`Node.decEq`), structural equality, rather than the derived `BEq`, whose laws
cannot be proved. -/
def addMono (p : Poly) (m : Mono) (c : Rat) : Poly :=
  if c = 0 then p
  else match p.find? (fun e => decide (e.1 = m)) with
    | some (_, d) =>
      let p := p.filter (fun e => !decide (e.1 = m))
      if c + d = 0 then p else p ++ [(m, c + d)]
    | none => p ++ [(m, c)]

def add (p q : Poly) : Poly := q.foldl (fun acc (m, c) => acc.addMono m c) p

def scale (p : Poly) (c : Rat) : Poly :=
  if c = 0 then [] else p.map fun (m, d) => (m, c * d)

def mul (p q : Poly) : Poly :=
  p.foldl (fun acc (m₁, c₁) =>
    q.foldl (fun acc (m₂, c₂) => acc.addMono (sortLeaves (m₁ ++ m₂)) (c₁ * c₂)) acc) []

def const (c : Rat) : Poly := Poly.addMono [] [] c

def constant (p : Poly) : Rat := ((p.find? (·.1 == [])).map (·.2)).getD 0

def removeConstant (p : Poly) : Poly := p.filter (·.1 != [])

def sorted (p : Poly) (o : NodeOrder := {}) : Poly := p.mergeSort fun a b => !monoLt b.1 a.1 o

/-- The leading (first non-constant) coefficient, in cvc5's order. -/
def leadingCoeff? (p : Poly) (o : NodeOrder := {}) : Option Rat := (((p.sorted o).find? (·.1 != [])).map (·.2))

/-- Whether every leaf is an integer (cvc5's `isIntegral`). -/
def isIntegral (p : Poly) : Bool := p.all fun (m, _) => m.all isInt

end Poly

/-- The polynomial of an arithmetic term (cvc5's `addToSum`, flattening through
`+`, `-`, `*`, unary `-`, `to_real` and division by a constant). -/
def polyOf (n : Node) : Poly :=
  match n with
  | .const (.integer i) => .const i
  | .const (.rational q) => .const q
  | .app (.kind .ADD) cs => (cs.attach.toList.map fun ⟨c, _⟩ => polyOf c).foldl Poly.add []
  | .app (.kind .SUB) ⟨[a, b]⟩ => (polyOf a).add ((polyOf b).scale (-1))
  | .app (.kind .NEG) ⟨[a]⟩ => (polyOf a).scale (-1)
  | .app (.kind .MULT) cs =>
    (cs.attach.toList.map fun ⟨c, _⟩ => polyOf c).foldl Poly.mul (.const 1)
  | .app (.kind .TO_REAL) ⟨[a]⟩ => polyOf a
  | .app (.kind .DIVISION) ⟨[a, .const (.rational q)]⟩ =>
    if q == 0 then [([n], 1)] else (polyOf a).scale (1 / q)
  | .app (.kind .DIVISION) ⟨[a, .const (.integer i)]⟩ =>
    if i == 0 then [([n], 1)] else (polyOf a).scale (1 / (i : Rat))
  | n => [([n], 1)]
termination_by sizeOf n
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (simp_all; omega)

/-- A constant of the given arithmetic type. -/
def constNode (real : Bool) (c : Rat) : Node :=
  if real then .const (.rational c) else .const (.integer c.num)

/-- A leaf of a sum of type `Real` when `real`: integer leaves get `to_real`. -/
def wrapLeaf (real : Bool) (l : Node) : Node := if real && isInt l then mkNode .TO_REAL #[l] else l

/-- The product of factors: the factor itself when there is one. -/
def productNode : List Node → Node
  | [x] => x
  | xs => mkNode .MULT xs.toArray

def monoNode (real : Bool) (fs : Mono) : Node := productNode (fs.map (wrapLeaf real))

/-- The term `c * fs` of a sum of type `Real` when `real` (cvc5's `mkMultTerm`). -/
def termNode (real : Bool) : Mono × Rat → Node
  | ([], c) => constNode real c
  | (fs, c) =>
    if real && fs.all isInt then
      -- An integer monomial of a real sum: as cvc5 prints its mixed sums,
      -- `(to_real (* c m))` for an integral `c`, else `(* c (to_real m))`.
      if c.isInt then
        mkNode .TO_REAL #[if c = 1 then productNode fs else
          mkNode .MULT #[constNode false c, productNode fs]]
      else mkNode .MULT #[constNode true c, mkNode .TO_REAL #[productNode fs]]
    else if c = 1 then monoNode real fs else mkNode .MULT #[constNode real c, monoNode real fs]

/-- The node of a sum of terms. -/
def sumNode (real : Bool) : List Node → Node
  | [] => constNode real 0
  | [t] => t
  | ts => mkNode .ADD ts.toArray

/-- The node of a polynomial in cvc5's normal form (`collectSum`, `mkMultTerm`),
of type `Real` when `real`. -/
def Poly.toNodeAt (real : Bool) (p : Poly) (o : NodeOrder := {}) : Node :=
  sumNode real ((p.sorted o).map (termNode real))

/-- The node of a polynomial in cvc5's normal form. A real sum of integer leaves
with integral coefficients is an integer sum for cvc5 (`maybeEnsureReal`), so it
is `(to_real (+ (- 3) x))`. -/
def Poly.toNode (real : Bool) (p : Poly) (o : NodeOrder := {}) : Node :=
  if real && p.isIntegral && p.all (·.2.isInt) && p.any (·.1 != []) then
    mkNode .TO_REAL #[p.toNodeAt false o]
  else p.toNodeAt real o

/-- The normal form of an arithmetic term. -/
def arithNorm (n : Node) (o : NodeOrder := {}) : Node := (polyOf n).toNode (isReal n) o

/-- The conditions under which `(= n m)`, for `m = arithNorm n` and `p = polyOf n`,
is statically known to be an `arith_poly_norm` step, all cheap to decide: `n`
has an arithmetic type, the equation is well typed, and an integer normal form
has integer coefficients. `p` and `m` are arguments so that they are computed
once. -/
def ArithNormOk (n : Node) (p : Poly) (m : Node) : Prop :=
  (n.smtType = .Int ∨ n.smtType = .Real) ∧
    __smtx_typeof (__eo_to_smt (eqFormula n m)) = .Bool ∧
    (isReal n = true ∨ p.all (·.2.isInt) = true)

/-- Decided with `smtTypeF`, without translating to Logos (`smtTypeF_eq`). -/
instance (n : Node) (p : Poly) (m : Node) : Decidable (ArithNormOk n p m) :=
  let T := n.smtTypeF
  decidable_of_iff ((T = .Int ∨ T = .Real) ∧ __smtx_typeof_eq T m.smtTypeF = .Bool ∧
      (isReal n = true ∨ p.all (·.2.isInt) = true))
    (by simp only [T, ArithNormOk, Node.typeof_eqFormula, Node.smtTypeF_eq])

/-- The conditions under which `(= n m)` follows from the premise `(= a b)` by
`arith_poly_norm_rel`, with the premise statically known to be an
`arith_poly_norm` step: `a` has an arithmetic type, both equations are well
typed, `a` and `b` have the same telos polynomial up to the order of its
monomials (decided natively, without Logos's normalizer), and Logos's
`arith_poly_norm_rel` program, which only checks the shapes and the signs of the
constants, accepts the step. -/
def ArithRelOk (n m a b : Node) : Prop :=
  (a.smtType = .Int ∨ a.smtType = .Real) ∧
    __smtx_typeof (__eo_to_smt (eqFormula a b)) = .Bool ∧
    List.Perm (polyOf a) (polyOf b) ∧
    __smtx_typeof (__eo_to_smt (eqFormula n m)) = .Bool ∧
    __eo_prog_arith_poly_norm_rel (eqFormula n m) (Proof.pf (eqFormula a b)) = eqFormula n m

/-- Decided with `smtTypeF`, without translating to Logos (`smtTypeF_eq`). -/
instance (n m a b : Node) : Decidable (ArithRelOk n m a b) :=
  let T := a.smtTypeF
  decidable_of_iff ((T = .Int ∨ T = .Real) ∧ __smtx_typeof_eq T b.smtTypeF = .Bool ∧
      List.Perm (polyOf a) (polyOf b) ∧ __smtx_typeof_eq n.smtTypeF m.smtTypeF = .Bool ∧
      __eo_prog_arith_poly_norm_rel (eqFormula n m) (Proof.pf (eqFormula a b)) = eqFormula n m)
    (by simp only [T, ArithRelOk, Node.typeof_eqFormula, Node.smtTypeF_eq])

end Telos.Arith
