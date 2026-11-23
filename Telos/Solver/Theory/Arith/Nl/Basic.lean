import Telos.Rewriter.Rewrite
import Telos.Core.Node.Print
import Telos.Solver.Theory.Arith.Poly

/-!
# Nonlinear arithmetic: monomial sums and the monomial database

The data structures of cvc5's nonlinear extension (`src/theory/arith/nl/`)
that are not tied to its state:
- `ArithMSum` (`src/theory/arith/arith_msum.cpp`): a term as a sum of
  monomials with coefficients, keyed by the monomial (`std::map<Node, Node>`,
  so in cvc5's node order, the constant first);
- `ArithSubs` (`arith_subs.cpp`): substitutions applied below arithmetic
  operators only;
- `MonomialDb` (`ext/monomial.cpp`): the exponents, variable lists and degrees
  of monomials, and which monomials divide which.

A monomial is a product of at least two non-constant factors, cvc5's
`NONLINEAR_MULT`, which telos writes as `MULT` without a constant (`isNlMult`):
the rewriter's normal form puts a coefficient first, and a product of a
constant and one term is cvc5's `MULT`.

Where cvc5 iterates over a `std::map<Node, _>` or sorts nodes with
`operator<`, it goes by node id, which telos approximates (`NodeOrder`).

Untrusted: these decide which lemmas the extension sends, and each lemma is
certified when it is sent (`Telos/Solver/NlLemma.lean`).
-/

namespace Telos.Solver.Arith.Nl

/-- cvc5's `NONLINEAR_MULT`: a product of at least two factors, none a
constant. -/
def isNlMult : Node → Bool
  | .app (.kind .MULT) cs => cs.size ≥ 2 && cs.all (fun c => (constVal? c).isNone)
  | _ => false

/-- An arithmetic term of type `Real`. -/
def isRealTerm (n : Node) : Bool := n.typeHint == some .real

/-- An arithmetic term (of type `Int` or `Real`). -/
def isArithTerm (n : Node) : Bool := n.typeHint == some .real || n.typeHint == some .integer

/-- `mkConstRealOrInt(r)`: an integer if integral, else a real. -/
def mkConstQ (q : Rat) : Node := Telos.Arith.constNode (q.den != 1) q

/-- `mkConstRealOrInt(T, r)`: a constant of the type of `t` (a real when
`q` is not integral). -/
def mkConstOf (t : Node) (q : Rat) : Node := Telos.Arith.constNode (isRealTerm t || q.den != 1) q

/-- `mkZero(T)`. -/
def zeroOf (t : Node) : Node := mkConstOf t 0
/-- `mkOne(T)`. -/
def oneOf (t : Node) : Node := mkConstOf t 1

/-- `castToReal`: `(to_real t)` for an integer term (constants are cast). -/
def castToReal (t : Node) : Node :=
  match constVal? t with
  | some q => .const (.rational q)
  | none => if isRealTerm t then t else Node.mkNode .TO_REAL #[t]

/-- The kinds whose terms `ArithSubs` and the model traverse: those of
arithmetic, the Booleans and builtins (`shouldTraverse`). -/
def traverses (n : Node) : Bool :=
  match n with
  | .app (.kind k) _ =>
    k == .EQUAL || k == .DISTINCT ||
      (match k.theoryId with
        | .THEORY_ARITH | .THEORY_BOOL | .THEORY_BUILTIN => true
        | _ => false) &&
      -- (the extended nonlinear kinds are black boxes)
      k != .POW2 && k != .INTS_LOG2 && k != .INTS_ISPOW2
  | _ => false

/-! ## Monomial sums (`ArithMSum`) -/

/-- A monomial sum: monomials (`none`: the constant) with their coefficients
(`none`: 1, cvc5's null coefficient), sorted by node order, the constant
first. -/
abbrev MSum := Array (Option Node × Option Node)

namespace MSum

def keyLt (o : NodeOrder) : Option Node → Option Node → Bool
  | none, some _ => true
  | some a, some b => o.lt a b
  | _, _ => false

def get? (m : MSum) (k : Option Node) : Option (Option Node) :=
  (Array.find? (·.1 == k) m).map (·.2)

def contains (m : MSum) (k : Option Node) : Bool := m.any (·.1 == k)

/-- `msum[k] = v`. -/
def set (o : NodeOrder) (m : MSum) (k : Option Node) (v : Option Node) : MSum :=
  match m.findIdx? (·.1 == k) with
  | some i => m.set! i (k, v)
  | none =>
    let i := (m.findIdx? fun (k', _) => keyLt o k k').getD m.size
    m.insertIdx! i (k, v)

def erase (m : MSum) (k : Option Node) : MSum := m.filter (·.1 != k)

/-- The value of a coefficient (`none` is 1). -/
def coeffVal (c : Option Node) : Rat := ((c.bind constVal?)).getD 1

/-- `getMonomial`: add the monomial `n`, unless its key is there already. -/
def getMonomial (o : NodeOrder) (n : Node) (m : MSum) : Option MSum :=
  if (constVal? n).isSome then
    if m.contains none then none else some (set o m none (some n))
  else match n with
    | .app (.kind .MULT) #[c, v] =>
      if (constVal? c).isSome then
        if m.contains (some v) then none else some (set o m (some v) (some c))
      else if m.contains (some n) then none else some (set o m (some n) none)
    | _ => if m.contains (some n) then none else some (set o m (some n) none)

/-- `getMonomialSum`. -/
def getMonomialSum (o : NodeOrder) (n : Node) (m : MSum := #[]) : Option MSum :=
  match n with
  | .app (.kind .ADD) cs => cs.foldlM (fun m c => getMonomial o c m) m
  | _ => getMonomial o n m

/-- `getMonomialSumLit`: of `(>= a b)` or of an arithmetic `(= a b)`, the sum
of `a - b`. -/
def getMonomialSumLit (o : NodeOrder) (lit : Node) : Option MSum := do
  let (a, b) ← match lit with
    | .app (.kind .GEQ) #[a, b] => some (a, b)
    | .app (.kind .EQUAL) #[a, b] => if isArithTerm a then some (a, b) else none
    | _ => none
  let m ← getMonomialSum o a
  if constVal? b == some 0 then return m
  let m2 ← getMonomialSum o b
  let mut m := m
  for (k, v) in m2 do
    match get? m k with
    | some v1 => m := set o m k (some (mkConstQ (coeffVal v1 - coeffVal v)))
    | none => m := set o m k (some (match v with
        | none => .const (.integer (-1))
        | some c => mkConstQ (-(coeffVal (some c)))))
  return m

/-- `mkCoeffTerm`: `c * t` (`t` if the coefficient is null), casting an
integer `t` to real for a non-integral coefficient. -/
def mkCoeffTerm (c : Option Node) (t : Node) : Node :=
  match c with
  | none => t
  | some c =>
    let r := coeffVal (some c)
    if r.den != 1 && !isRealTerm t then Node.mkNode .MULT #[c, Node.mkNode .TO_REAL #[t]]
    else Node.mkNode .MULT #[mkConstOf t r, t]

/-- `ArithMSum::mkNode`. -/
def toNode (m : MSum) : Node :=
  let cs := m.map fun (k, v) => match k with
    | some t => mkCoeffTerm v t
    | none => v.getD (.const (.integer 0))
  if cs.size > 1 then Node.mkNode .ADD cs
  else cs[0]?.getD (.const (.integer 0))

/-- `isolate(v, msum, veq_c, val, k)`: `v` isolated, with the result `1`
(`v k val`, scaled by `veq_c`), `-1` (`val k v`) or `0` (not possible); the
coefficient `veq_c` is set for an integer `v` with a coefficient other than
±1. -/
def isolate (v : Node) (m : MSum) (k : Kind) : Int × Option Node × Node := Id.run do
  let some cv := get? m (some v) | return (0, none, default)
  let real := isRealTerm v
  let r := coeffVal cv
  if r == 0 then return (0, none, default)
  let mut children : Array Node := #[]
  for (k', c) in m do
    if k' == some v then continue
    let t := match k' with
      | some t => mkCoeffTerm c t
      | none => c.getD (.const (.integer 0))
    children := children.push (if real && !isRealTerm t then castToReal t else t)
  let mut val := if children.size > 1 then Node.mkNode .ADD children
    else children[0]?.getD (mkConstOf v 0)
  let mut veqc := none
  if r != 1 && r != -1 then
    if !real then veqc := some (mkConstQ (if r < 0 then -r else r))
    else val := Node.mkNode .MULT #[val, .const (.rational (1 / (if r < 0 then -r else r)))]
  if r > 0 then val := Node.mkNode .MULT #[mkConstOf val (-1), val]
  return ((if r > 0 || k == .EQUAL then 1 else -1), veqc, val)

end MSum

/-! ## Substitutions below arithmetic (`ArithSubs`) -/

/-- `ArithSubs`: variables and their substitutes, in order. -/
structure ArithSubs where
  vars : Array Node := #[]
  subs : Array Node := #[]
  deriving Inhabited

namespace ArithSubs

def isEmpty (s : ArithSubs) : Bool := s.vars.isEmpty
def get? (s : ArithSubs) (v : Node) : Option Node :=
  (s.vars.findIdx? (· == v)).map fun i => s.subs[i]!
def contains (s : ArithSubs) (v : Node) : Bool := s.vars.contains v
def add (s : ArithSubs) (v t : Node) : ArithSubs := { vars := s.vars.push v, subs := s.subs.push t }

/-- `applyArith`: the substitution below the operators of arithmetic, the
Booleans and builtins (not below other theories' applications). -/
partial def apply (s : ArithSubs) (n : Node) : Node :=
  if s.isEmpty then n else go n
where
  go (n : Node) : Node :=
    match s.get? n with
    | some t => t
    | none =>
      match n with
      | .app op cs => if traverses n then .app op (cs.map go) else n
      | _ => n

/-- `hasArithSubterm`: `t` occurs in `n` below arithmetic operators. -/
partial def hasArithSubterm (n t : Node) : Bool :=
  n == t || match n with
    | .app _ cs => traverses n && cs.any (hasArithSubterm · t)
    | _ => false

end ArithSubs

/-! ## The monomial database (`MonomialDb`) -/

/-- `MonomialIndex`: a trie of variable lists, for the monomials that divide
others. -/
inductive MIndex where
  | mk (data : Array (Node × MIndex)) (monos : Array Node)
  deriving Inhabited

/-- `MonomialRelation`. -/
inductive MRel where
  | equal | superset | subset | invalid
  deriving BEq, Inhabited

/-- The database of monomials. -/
structure MonomialDb where
  /-- `d_monomials`, in order of registration. -/
  monomials : Array Node := #[]
  registered : Std.HashSet Key := {}
  /-- `d_m_exp`: each factor and its exponent, in node order. -/
  exp : Std.HashMap Key (Array (Node × Nat)) := {}
  /-- `d_m_vlist`: the distinct factors, in node order (re-sorted by the model,
  `sortVariablesByModel`). -/
  vlist : Std.HashMap Key (Array Node) := {}
  degree : Std.HashMap Key Nat := {}
  /-- `d_m_contain_parent`, `d_m_contain_children`: the monomials that `a`
  divides, and those that divide `b`. -/
  containParent : Std.HashMap Key (Array Node) := {}
  containChildren : Std.HashMap Key (Array Node) := {}
  /-- `d_m_contain_mult`, `d_m_contain_umult`: the quotient `b / a`, as a
  `MULT` and as a monomial. -/
  containMult : Std.HashMap (Key × Key) Node := {}
  containUMult : Std.HashMap (Key × Key) Node := {}
  index : MIndex := .mk #[] #[]
  deriving Inhabited

namespace MonomialDb

def getExp (db : MonomialDb) (m : Node) : Array (Node × Nat) := (db.exp.get? ⟨m⟩).getD #[]
def getVarList (db : MonomialDb) (m : Node) : Array Node := (db.vlist.get? ⟨m⟩).getD #[]
def getDegree (db : MonomialDb) (m : Node) : Nat := (db.degree.get? ⟨m⟩).getD 0

/-- `getExponent`. -/
def getExponent (db : MonomialDb) (m v : Node) : Nat :=
  ((db.getExp m).find? (·.1 == v)).map (·.2) |>.getD 0

def countIn (e : Array (Node × Nat)) (v : Node) : Nat := ((e.find? (·.1 == v)).map (·.2)).getD 0

/-- `isMonomialSubset a b`: `a` divides `b`. -/
def isSubset (db : MonomialDb) (a b : Node) : Bool :=
  let eb := db.getExp b
  (db.getExp a).all fun (v, n) => n ≤ countIn eb v

/-- `ExpandMultiset(diffMultiset(b, a))`: the factors of `b` not in `a`, with
repetitions, in node order. -/
def diffFactors (db : MonomialDb) (b a : Node) : Array Node := Id.run do
  let ea := db.getExp a
  let mut out := #[]
  for (v, n) in db.getExp b do
    let k := countIn ea v
    if n > k then
      for _ in [0:n - k] do out := out.push v
  return out

/-- `safeConstructNaryType(Real, k, cs)`: `1` for no factor, the factor for
one, the application otherwise. -/
def mkNary (k : Kind) (cs : Array Node) : Node :=
  if cs.isEmpty then .const (.rational 1)
  else if cs.size == 1 then cs[0]!
  else Node.mkNode k cs

/-- `registerMonomialSubset a b`. -/
def registerSubset (db : MonomialDb) (a b : Node) : MonomialDb :=
  let diff := db.diffFactors b a
  { db with
    containParent := db.containParent.insert ⟨a⟩ (((db.containParent.get? ⟨a⟩).getD #[]).push b)
    containChildren := db.containChildren.insert ⟨b⟩ (((db.containChildren.get? ⟨b⟩).getD #[]).push a)
    containMult := db.containMult.insert (⟨a⟩, ⟨b⟩) (mkNary .MULT diff)
    containUMult := db.containUMult.insert (⟨a⟩, ⟨b⟩) (mkNary .MULT diff) }

/-- `MonomialIndex::addTerm`: the index with `n` (of variable list `reps`)
added, and the pairs `(a, b)` with `a` dividing `b` found on the way, in
cvc5's order. -/
partial def addTerm (o : NodeOrder) (db : MonomialDb) (n : Node) (reps : Array Node) :
    MIndex → MRel → Nat → MIndex × Array (Node × Node)
  | .mk data monos, status, argIndex => Id.run do
    let mut data := data
    let mut monos := monos
    let mut pairs : Array (Node × Node) := #[]
    if status == .equal then
      if argIndex == reps.size then monos := monos.push n
      else
        let r := reps[argIndex]!
        match data.findIdx? (·.1 == r) with
        | some i =>
          let (c, ps) := addTerm o db n reps data[i]!.2 .equal (argIndex + 1)
          data := data.set! i (r, c)
          pairs := pairs ++ ps
        | none =>
          let (c, ps) := addTerm o db n reps (.mk #[] #[]) .equal (argIndex + 1)
          let i := (data.findIdx? fun (k, _) => o.lt r k).getD data.size
          data := data.insertIdx! i (r, c)
          pairs := pairs ++ ps
    for i in [0:data.size] do
      let (k, child) := data[i]!
      if status != .equal || argIndex == reps.size || k != reps[argIndex]! then
        let inQuery := reps.contains k
        let mut newStatus := status
        if !inQuery then newStatus := if status == .superset then .invalid else .subset
        else if status == .equal then newStatus := .superset
        if newStatus != .invalid then
          let (c, ps) := addTerm o db n reps child newStatus argIndex
          data := data.set! i (k, c)
          pairs := pairs ++ ps
    for m in monos do
      if m != n then
        let mut rel := status
        if rel == .equal && argIndex != reps.size then rel := .superset
        if (rel == .equal || rel == .superset) && db.isSubset m n then pairs := pairs.push (m, n)
        else if (rel == .equal || rel == .subset) && db.isSubset n m then pairs := pairs.push (n, m)
    return (.mk data monos, pairs)

/-- Sort by `lt` (stable). -/
def sortBy (xs : Array Node) (lt : Node → Node → Bool) : Array Node :=
  (xs.toList.mergeSort fun a b => !lt b a).toArray

/-- `registerMonomial`: a monomial, a variable or the constant `1`. -/
def register (o : NodeOrder) (db : MonomialDb) (n : Node) : MonomialDb := Id.run do
  if db.registered.contains ⟨n⟩ then return db
  let mut db := { db with monomials := db.monomials.push n, registered := db.registered.insert ⟨n⟩ }
  let (e, vl, d) : Array (Node × Nat) × Array Node × Nat :=
    if isNlMult n then
      let cs := n.getChildren
      let e := cs.foldl (fun (e : Array (Node × Nat)) c =>
        match e.findIdx? (·.1 == c) with
        | some i => e.modify i fun (c, k) => (c, k + 1)
        | none => e.push (c, 1)) #[]
      let vl := (Array.range cs.size).foldl (fun (vl : Array Node) i =>
        if i == 0 || cs[i]! != cs[i-1]! then vl.push cs[i]! else vl) #[]
      (e, vl, cs.size)
    else if (constVal? n).isSome then (#[], #[], 0)
    else (#[(n, 1)], #[n], 1)
  let e := (e.toList.mergeSort fun a b => !o.lt b.1 a.1).toArray
  let vl := sortBy vl o.lt
  db := { db with exp := db.exp.insert ⟨n⟩ e, vlist := db.vlist.insert ⟨n⟩ vl,
                  degree := db.degree.insert ⟨n⟩ d }
  let (idx, pairs) := addTerm o db n vl db.index .equal 0
  db := { db with index := idx }
  for (a, b) in pairs do db := db.registerSubset a b
  return db

/-- `getContainsDiff a b`: `b / a`, as a `MULT`. -/
def containsDiff? (db : MonomialDb) (a b : Node) : Option Node := db.containMult.get? (⟨a⟩, ⟨b⟩)
/-- `getContainsDiffNl a b`. -/
def containsDiffNl? (db : MonomialDb) (a b : Node) : Option Node := db.containUMult.get? (⟨a⟩, ⟨b⟩)

def parents (db : MonomialDb) (a : Node) : Option (Array Node) := db.containParent.get? ⟨a⟩
def children (db : MonomialDb) (b : Node) : Option (Array Node) := db.containChildren.get? ⟨b⟩

/-- `mkMonomialRemFactor(n, rem)`: `n` without the factors of `rem`, as a
`MULT` of the type of `n`. -/
def remFactor (db : MonomialDb) (n : Node) (rem : Array (Node × Nat)) : Node := Id.run do
  let mut cs := #[]
  for (v, k) in db.getExp n do
    let r := countIn rem v
    for _ in [0:k - r] do cs := cs.push v
  if cs.isEmpty then return oneOf n
  if cs.size == 1 then return cs[0]!
  return Node.mkNode .MULT cs

end MonomialDb

end Telos.Solver.Arith.Nl
