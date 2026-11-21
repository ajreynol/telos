import Telos.Rewriter.Rewrite
import Telos.Solver.LinCert
import Telos.Solver.Theory.Arith.Simplex

/-!
# Certificates of the linear solver's conflicts and lemmas

The refutations (`Telos/Solver/LinCert.lean`) of the solver's conflicts, of
the clauses of its lemmas, and of the explanations of its propagations, built
from the proofs of its constraints (cvc5's `ConstraintRule`s), as cvc5's proof
production reads them (`Constraint::externalExplain`, with proofs):
- an assumption of the explanation (where `explainInto` stops) is its
  literal (its witness);
- a constraint derived by a Farkas rule (`farkas`, and the unate rules) is a
  Farkas combination of its antecedents and its negation, with the rule's
  coefficients;
- one derived by trichotomy is refuted with its antecedents by a split of the
  disequality among them, each side being refuted by two of the literals;
- a derived antecedent is introduced by a cut on its literal, whose negative
  side refutes the constraint's negation with its own antecedents.

The coefficients are cvc5's, for the bounds `x ⋈ v` of the constraints:
negative for a lower bound, positive for an upper bound, so that
`Σ cᵢ (xᵢ - vᵢ)` is a constant that is not `≤ 0`. A literal bounds the
difference `d` of its sides (`linParts`), with `d = α (x - v)`; its coefficient
in the certificate is `-c / α`. Nothing here is trusted: the certificates are
checked.
-/

namespace Telos.Solver.Arith

open State

/-- The polynomial of `a - b` (through `to_real`). -/
def linPoly (a b : Node) : Telos.Arith.Poly := Telos.Arith.polyOf (Node.mkNode .SUB #[a, b])

def coeffOf (p : Telos.Arith.Poly) (m : Telos.Arith.Mono) : Rat :=
  ((p.find? fun e => decide (e.1 = m)).map (·.2)).getD 0

/-- The first non-constant monomial of a polynomial, with its coefficient. -/
def firstMono (p : Telos.Arith.Poly) : Option (Telos.Arith.Mono × Rat) := p.find? (·.1 != [])

/-- The entry of the literal `l` of a bound of `x` with cvc5's coefficient `f`. -/
def farkasCoeff (s : State) (x : Nat) (l : Node) (f : Rat) : Option (Node × Rat) := do
  let (a, b, _) ← linParts l
  let (m, cx) ← firstMono (Telos.Arith.polyOf (s.var x).node)
  let alpha := coeffOf (linPoly a b) m / cx
  if alpha == 0 then none
  pure (l, -f / alpha)

/-- A Farkas combination of two literals, found from their polynomials. -/
def pairFarkas (l1 l2 : Node) : Option LinCert := do
  let (a1, b1, _) ← linParts l1
  let (a2, b2, _) ← linParts l2
  let (m, c1) ← firstMono (linPoly a1 b1)
  let c2 := coeffOf (linPoly a2 b2) m
  if c2 == 0 then none
  let r := -c1 / c2
  let cands : List (Array (Node × Rat)) := [#[(l1, 1), (l2, r)], #[(l1, -1), (l2, -r)]]
  (cands.find? (checkFarkas #[l1, l2])).map .farkas

/-- A refutation of a few literals: by cases on a negated conjunction among
them, by a split of a disequality, and then of two of them. -/
partial def smallRefute (lits : Array Node) : Option LinCert :=
  match lits.findIdx? (fun l => (notAndParts l).isSome) with
  | some i => do
    let l := lits[i]!
    let cs ← notAndParts l
    let rest := lits.eraseIdx! i
    let subs ← cs.mapM fun c => return (c, ← smallRefute (rest.push (negate c)))
    pure (.cases l subs)
  | none =>
  match lits.findIdx? (fun l => (diseqParts l).isSome) with
  | some i => do
    let l := lits[i]!
    let (a, b) ← diseqParts l
    let rest := lits.eraseIdx! i
    let lt ← smallRefute (rest.push (Node.mkNode .LT #[a, b]))
    let gt ← smallRefute (rest.push (Node.mkNode .GT #[a, b]))
    pure (.split l lt gt)
  | none => Id.run do
    for i in [0:lits.size] do
      for j in [i+1:lits.size] do
        if let some p := pairFarkas lits[i]! lits[j]! then return some p
    return none

/-- The literal of an assumption of an explanation (where `explainInto` stops),
for the assertion order `order`. -/
def leafLit (s : State) (c : Nat) (order : Option Nat) : Option Node :=
  let k := s.constraint c
  let before := match order with
    | none => k.assertedToTheTheory
    | some o => k.assertedBefore o
  if before then k.witness else none

/-- A constraint's literal; built (`x ⋈ v`) if it has none. -/
def litOf (s : State) (c : Nat) : Node :=
  let k := s.constraint c
  match k.literal with
  | some l => l
  | none =>
    let p := (s.var k.var).node
    -- an integer variable: an integer constant, or its real value
    let (p, v) :=
      if s.isInteger k.var then
        if k.value.c.den == 1 then (p, Node.const (.integer k.value.c.num))
        else (Node.mkNode .TO_REAL #[p], ratNode k.value.c)
      else (p, ratNode k.value.c)
    match k.type with
    | .lowerBound => Node.mkNode (if k.value.k > 0 then .GT else .GEQ) #[p, v]
    | .upperBound => Node.mkNode (if k.value.k < 0 then .LT else .LEQ) #[p, v]
    | .equality => Node.mkNode .EQUAL #[p, v]
    | .disequality => Node.notNode (Node.mkNode .EQUAL #[p, v])

/-- The antecedents of a rule, in order. -/
def antecedentsOf (s : State) (r : ConstraintRule) : Array Nat := Id.run do
  let mut out := #[]
  let mut p := r.antecedentEnd
  repeat
    match p with
    | some i =>
      match s.antecedents[i]! with
      | some a =>
        out := out.push a
        p := if i == 0 then none else some (i - 1)
      | none => break
    | none => break
  return out.reverse

mutual
/-- Refute the antecedents of `c` (down to the assumptions of the explanation)
with `negLit`, the negation of the literal of `c`. -/
partial def refute (s : State) (c : Nat) (order : Option Nat) (negLit : Node) : Option LinCert := do
  let r ← s.rule c
  let ants := antecedentsOf s r
  match r.proofType with
  | .farkas => farkasCert s order c negLit ants (← r.farkas)
  | .trichotomy | .intTighten => withLits s order ants.toList #[] fun ls => smallRefute (ls.push negLit)
  | _ => none

/-- The Farkas combination of a rule: `negLit` for the negation of `c`, and the
antecedents. -/
partial def farkasCert (s : State) (order : Option Nat) (c : Nat) (negLit : Node) (ants : Array Nat)
    (f : Array Rat) : Option LinCert :=
  withLits s order ants.toList #[] fun ls => do
    if f.size != ants.size + 1 then none
    let e0 ← farkasCoeff s (s.constraint c).var negLit f[0]!
    let mut es := #[e0]
    for i in [0:ants.size] do
      es := es.push (← farkasCoeff s (s.constraint ants[i]!).var ls[i]! f[i+1]!)
    pure (.farkas es)

/-- The literals of the antecedents `ants`, the derived ones introduced by cuts;
`k` refutes them. -/
partial def withLits (s : State) (order : Option Nat) (ants : List Nat) (acc : Array Node)
    (k : Array Node → Option LinCert) : Option LinCert :=
  match ants with
  | [] => k acc
  | a :: rest =>
    match leafLit s a order with
    | some w => withLits s order rest (acc.push w) k
    | none => do
      let l := litOf s a
      let pos ← withLits s order rest (acc.push l) k
      let neg ← refute s a order (negate l)
      pure (.cut l pos neg)
end

/-- The certificate of a conflict on `c` (`explainConflict`): `c` and its
negation, each with its antecedents. -/
def conflictCert (s : State) (c : Nat) : Option LinCert :=
  withLits s none [c, (s.constraint c).negation] #[] smallRefute

/-- The certificate of the explanation of the propagated literal `lit`
(`explain`): it refutes the explanation with the negation of `lit`. -/
def propagationCert (s : State) (lit : Node) : Option LinCert := do
  let c ← s.lookup lit
  refute s c (s.constraint c).assertionOrder (negate lit)

/-- The certificate of a clause `(or l₁ … lₙ)` of literals: a refutation of
their negations. -/
def clauseCert (lits : Array Node) : Option LinCert := smallRefute (lits.map negate)

/-- The entry of the input equation `P = 0` (`P` a polynomial) with the weight
`w`, by one of the literals of its bounds: `P` is `α` times the difference of
its sides, so its coefficient is `w / α`, nonnegative unless it is an
equality. -/
def eqEntry (lits : Array Node) (P : Telos.Arith.Poly) (w : Rat) : Option (Node × Rat) := do
  let (m, cp) ← firstMono P
  lits.findSome? fun l => do
    let (a, b, r) ← linParts l
    let alpha := coeffOf (linPoly a b) m / cp
    if alpha == 0 then none
    let q := w / alpha
    if r == .eq || q ≥ 0 then some (l, q) else none

/-- The certificate of a conflict of the Diophantine solver: the input
equations `Pⱼ = 0` (with their constraints) combine, with the weights `μⱼ`,
into `E = g Q + k = 0`, where `Q` has coprime integer coefficients and `g`
does not divide `k` (or `E` is a nonzero constant). With `r = -k / g`, which is
not an integer, a cut on `Q ≥ ⌈r⌉`: then `Q - ⌈r⌉ ≥ 0` and `-(Q - r) = 0` sum
to `r - ⌈r⌉ < 0`; otherwise `Q ≤ ⌈r⌉ - 1` (an integer) and `Q - r = 0` sum to
`⌈r⌉ - 1 - r < 0`. -/
def dioConflictCert (s : State) (ins : Array (Array Nat × Telos.Arith.Poly × Rat)) : Option LinCert :=
  let cons := ins.foldl (fun acc (cs, _, _) => acc ++ cs) #[]
  withLits s none cons.toList #[] fun ls => do
    -- the literals of each input's constraints
    let mut litsOf : Array (Array Node) := #[]
    let mut i := 0
    for (cs, _, _) in ins do
      litsOf := litsOf.push (ls.extract i (i + cs.size))
      i := i + cs.size
    let E := ins.foldl (fun acc (_, P, mu) => Telos.Arith.Poly.add acc (Telos.Arith.Poly.scale P mu))
      ([] : Telos.Arith.Poly)
    let terms := Telos.Arith.Poly.removeConstant E
    let k := Telos.Arith.Poly.constant E
    let entries (kappa : Rat) : Option (Array (Node × Rat)) :=
      (ins.zip litsOf).filterMapM fun ((_, P, mu), lits) =>
        if mu == 0 then pure none else (eqEntry lits P (kappa * mu)).map some
    if terms.isEmpty then
      if k == 0 then none
      pure (.farkas (← entries (if k > 0 then -1 else 1)))
    else
      let g : Rat := (terms.foldl (fun (g : Nat) (_, c) => Nat.gcd g c.num.natAbs) 0 : Nat)
      if g == 0 then none
      let r := -k / g
      if r.den == 1 then none
      let Q := (Poly.mk ((Telos.Arith.Poly.sorted (terms.map fun (m, c) => (m, c / g))).toArray.map
        fun (m, c) => (c, Telos.Arith.monoKey m))).node
      let L := Node.mkNode .GEQ #[Q, Node.const (.integer r.ceil)]
      let pos ← entries (-1 / g)
      let neg ← entries (1 / g)
      pure (.cut L (.farkas (#[(L, 1)] ++ pos)) (.farkas (#[(negate L, 1)] ++ neg)))

end Telos.Solver.Arith
