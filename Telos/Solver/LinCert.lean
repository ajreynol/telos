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
- `split l lt gt`: `l` is a disequality `(not (= a b))` of `A` (of reals or of
  integers), so `a < b` or `a > b`: `lt` refutes `A` with `(< a b)`, and `gt` refutes it with `(> a b)`.
- `cut l pos neg`: `l` is true or false, so `pos` refutes `A` with `l`, and
  `neg` refutes it with the negation of `l`. Cuts introduce the constraints
  that the solver derived.
- `cases l subs`: `l` is a negated conjunction `(not (and c₁ … cₙ))` of `A`, so
  some `cᵢ` is false: each `cᵢ` has an entry `(cᵢ, p)` of `subs`, where `p`
  refutes `A` with the negation of `cᵢ`.

The sides of a literal are real terms, or integer terms, whose difference is
made real (`to_real`): an integer bound `d > 0` is `d - 1 ≥ 0`, which is how
integer reasoning (tightening, branches, cuts) is certified.
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
def isRealTerm (t : Node) : Bool := t.smtTypeF == SmtType.Real

/-- A term of type `Int`. -/
def isIntTerm (t : Node) : Bool := t.smtTypeF == SmtType.Int

/-- A rational constant. -/
def ratNode (q : Rat) : Node := .const (.rational q)

/-- The term `(* q (- a b))`. -/
def linTerm (q : Rat) (a b : Node) : Node := Node.mkNode .MULT #[ratNode q, Node.mkNode .SUB #[a, b]]

/-- The real difference of integers `(to_real (- a b))`, less `1` if `strict`
(an integer `d > 0` is `≥ 1`). -/
def intDiff (a b : Node) (strict : Bool) : Node :=
  let d := Node.mkNode .TO_REAL #[Node.mkNode .SUB #[a, b]]
  if strict then Node.mkNode .SUB #[d, ratNode 1] else d

/-- The term `(* q d)` of an integer difference. -/
def intLinTerm (q : Rat) (a b : Node) (strict : Bool) : Node :=
  Node.mkNode .MULT #[ratNode q, intDiff a b strict]

/-- An entry of a Farkas combination: its term, and whether its bound is strict
(with a positive coefficient). -/
def farkasEntry (A : Array Node) (e : Node × Rat) : Option (Node × Bool) :=
  match linParts e.1 with
  | some (a, b, r) =>
    if A.contains e.1 && (r == .eq || decide (0 ≤ e.2)) then
      if isRealTerm a && isRealTerm b then some (linTerm e.2 a b, r == .gt && decide (0 < e.2))
      -- integers: a strict bound is strengthened, and is not strict any more
      else if isIntTerm a && isIntTerm b then some (intLinTerm e.2 a b (r == .gt), false)
      else none
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
  | cases (l : Node) (subs : Array (Node × LinCert))
  deriving Inhabited

/-- The conjuncts of a negated conjunction `(not (and c₁ … cₙ))`. -/
def notAndParts : Node → Option (Array Node)
  | .app (.kind k) cs =>
    if k == .NOT then
      if h : cs.size = 1 then
        match cs[0] with
        | .app (.kind k') ds => if k' == .AND && 2 ≤ ds.size then some ds else none
        | _ => none
      else none
    else none
  | _ => none

/-- **The certificate refutes `A`.** -/
def LinCert.check (A : Array Node) : LinCert → Bool
  | .farkas cs => checkFarkas A cs
  | .split l lt gt =>
    match diseqParts l with
    | some (a, b) =>
      A.contains l && ((isRealTerm a && isRealTerm b) || (isIntTerm a && isIntTerm b)) &&
        lt.check (A.push (Node.mkNode .LT #[a, b])) && gt.check (A.push (Node.mkNode .GT #[a, b]))
    | none => false
  | .cut l pos neg =>
    l.smtTypeF == SmtType.Bool && pos.check (A.push l) && neg.check (A.push (negate l))
  | .cases l subs =>
    match notAndParts l with
    | some cs =>
      A.contains l && (cs.all fun c => subs.any fun e => decide (e.1 = c)) &&
        subs.attach.all fun ⟨(c, p), _⟩ =>
          c.smtTypeF == SmtType.Bool && p.check (A.push (negate c))
    | none => false
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_›; simp_all; omega)

end Telos.Solver
