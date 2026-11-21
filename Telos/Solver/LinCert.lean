import Telos.Solver.EqProof
import Telos.Core.Node.FastType

/-!
# Linear-arithmetic refutations

A certificate that a set of arithmetic literals `A` is unsatisfiable over the
reals: the certificate of a conflict of the linear solver, and of the clauses
of its lemmas (refuting the negations of their literals). It is built after
the fact, from the solver's proofs of its constraints, which are cvc5's
(`Telos/Solver/Theory/Arith/Cert.lean`).

`LinCert.check A p` is a small function on nodes; its soundness is proved in
`verification/TelosProofs/Solver/LinCert.lean`. The rules:
- `farkas cs`: a Farkas combination. Each `(l, q)` of `cs` is a literal `l` of
  `A` with a coefficient `q`. A literal bounds the difference `d = a - b` of
  its sides (`linParts`): `d ≥ 0`, `d > 0`, or `d = 0`. The coefficients of
  the bounds are nonnegative, so that the sum `S` of the terms `q · d` is
  `≥ 0`, or `> 0` if a strict bound has a positive coefficient. The rewriter,
  which is proved correct, must rewrite that comparison of `S` with `0` to
  `false`: its polynomial normal form makes `S` a constant.
- `split l lt gt`: `l` is a disequality `(not (= a b))` of `A`, so `a < b` or
  `a > b`: `lt` refutes `A` with `(< a b)`, and `gt` refutes it with `(> a b)`.
- `cut l pos neg`: `l` is true or false, so `pos` refutes `A` with `l`, and
  `neg` refutes it with the negation of `l`. Cuts introduce the constraints
  that the solver derived.

The sides of the literals are real terms; integers are not supported yet.
-/

open Eo Smtm SmtEval

namespace Telos.Solver

/-- How a literal bounds the difference of its sides. -/
inductive LinRel where
  | ge | gt | eq
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The comparison `(k a b)`, as a bound of `a' - b'`: `(a', b', rel)`. -/
def cmpParts (k : Kind) (a b : Node) : Option (Node × Node × LinRel) :=
  match k with
  | .GEQ => some (a, b, .ge)
  | .GT => some (a, b, .gt)
  | .LEQ => some (b, a, .ge)
  | .LT => some (b, a, .gt)
  | .EQUAL => some (a, b, .eq)
  | _ => none

/-- The negation of the comparison `(k a b)`, as a bound. -/
def negParts (k : Kind) (a b : Node) : Option (Node × Node × LinRel) :=
  match k with
  | .GEQ => some (b, a, .gt)
  | .GT => some (b, a, .ge)
  | .LEQ => some (a, b, .gt)
  | .LT => some (a, b, .ge)
  | _ => none

/-- The bound that a literal is: a comparison, or the negation of an
inequality. -/
def linParts : Node → Option (Node × Node × LinRel)
  | .app (.kind k) cs =>
    if k == .NOT then
      if h : cs.size = 1 then
        match cs[0] with
        | .app (.kind k') ds => if h' : ds.size = 2 then negParts k' ds[0] ds[1] else none
        | _ => none
      else none
    else if h : cs.size = 2 then cmpParts k cs[0] cs[1] else none
  | _ => none

/-- The sides of a disequality `(not (= a b))`. -/
def diseqParts : Node → Option (Node × Node)
  | .app (.kind k) cs =>
    if k == .NOT then
      if h : cs.size = 1 then
        match cs[0] with
        | .app (.kind k') ds => if k' == .EQUAL then (if h' : ds.size = 2 then some (ds[0], ds[1]) else none) else none
        | _ => none
      else none
    else none
  | _ => none

/-- A term of type `Real`. -/
def isRealTerm (t : Node) : Bool := __smtx_typeof t.toSmt == SmtType.Real

/-- A rational constant. -/
def ratNode (q : Rat) : Node := .const (.rational q)

/-- The term `(* q (- a b))`. -/
def linTerm (q : Rat) (a b : Node) : Node := Node.mkNode .MULT #[ratNode q, Node.mkNode .SUB #[a, b]]

/-- An entry of a Farkas combination: its term, and whether its bound is strict
(with a positive coefficient). -/
def farkasEntry (A : Array Node) (e : Node × Rat) : Option (Node × Bool) :=
  match linParts e.1 with
  | some (a, b, r) =>
    if A.contains e.1 && isRealTerm a && isRealTerm b && (r == .eq || decide (0 ≤ e.2)) then
      some (linTerm e.2 a b, r == .gt && decide (0 < e.2))
    else none
  | none => none

/-- The comparison of the sum of the terms with `0`: `(> S 0)` if a bound is
strict, `(>= S 0)` otherwise, for `S = (+ 0 t₁ … tₙ)`. -/
def farkasAtom (ts : Array (Node × Bool)) : Node :=
  let S := Node.mkNode .ADD (#[ratNode 0] ++ ts.map (·.1))
  Node.mkNode (if ts.any (·.2) then .GT else .GEQ) #[S, ratNode 0]

/-- A Farkas combination of literals of `A` checks: its comparison is well
typed and rewrites to `false`. -/
def checkFarkas (A : Array Node) (cs : Array (Node × Rat)) : Bool :=
  match cs.mapM (farkasEntry A) with
  | some ts =>
    !ts.isEmpty && (let F := farkasAtom ts; decide F.WellTyped && Telos.rewrite F == Node.mkFalse)
  | none => false

/-- A refutation of a set of linear-arithmetic literals. -/
inductive LinCert where
  | farkas (cs : Array (Node × Rat))
  | split (l : Node) (lt gt : LinCert)
  | cut (l : Node) (pos neg : LinCert)
  deriving Inhabited

/-- **The certificate refutes `A`.** -/
def LinCert.check (A : Array Node) : LinCert → Bool
  | .farkas cs => checkFarkas A cs
  | .split l lt gt =>
    match diseqParts l with
    | some (a, b) =>
      A.contains l && isRealTerm a && isRealTerm b &&
        lt.check (A.push (Node.mkNode .LT #[a, b])) && gt.check (A.push (Node.mkNode .GT #[a, b]))
    | none => false
  | .cut l pos neg =>
    __smtx_typeof l.toSmt == SmtType.Bool && pos.check (A.push l) && neg.check (A.push (negate l))

/-- The number of Farkas combinations (for statistics). -/
def LinCert.size : LinCert → Nat
  | .farkas _ => 1
  | .split _ a b => a.size + b.size
  | .cut _ a b => a.size + b.size

end Telos.Solver
