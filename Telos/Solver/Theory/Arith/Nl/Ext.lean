import Telos.Solver.Theory.Arith.Nl.Model
import Telos.Solver.Rand

/-!
# The nonlinear extension

A port of cvc5's `NonlinearExtension` (`src/theory/arith/nl/`) in the
configuration of safe mode: `nl-ext=full` with its default techniques, no
coverings (`nl-cov` is off in safe mode), no ICP, no transcendental functions,
`iand` or `pow2` (excluded by safe mode), no splitting on zero
(`nl-ext-split-zero` is an expert option, off).

The linear solver treats each monomial (a product of variables, cvc5's
`NONLINEAR_MULT`) as a variable of its own. At full effort, when the linear
solver has a model, the extension (`checkFullEffort`) checks that model
against the monomials: it computes the abstract value of each term (its own
value in the linear model) and the concrete one (from the values of its
factors), and for the assertions that are false concretely runs its strategy
(`Strategy::initializeStrategy`), whose steps add lemmas:
- `NL_INIT`: the monomials and their variables (`ExtState::init`), the
  monomial database;
- `NL_MONOMIAL_SIGN`: the sign of a monomial from the signs of its factors
  (`MonomialCheck::checkSign`, `ARITH_NL_SIGN`);
- `NL_MONOMIAL_MAGNITUDE0/1/2`: comparisons of the magnitudes of monomials
  with `1`, with variables and with each other (`checkMagnitude`,
  `ARITH_NL_COMPARISON`);
- `NL_FLATTEN_MON`: monomials equal modulo the equality engine
  (`FlattenMonomialCheck`, `ARITH_NL_FLATTEN_MON`);
- `NL_MONOMIAL_INFER_BOUNDS`: bounds multiplied by the sign of a factor
  (`MonomialBoundsCheck::checkBounds`, `ARITH_NL_INFER_BOUNDS_NT`), and, in
  pure integer logics, tangent planes interleaved;
- then, as a last resort, the waiting lemmas, factoring (`FactoringCheck`,
  `ARITH_NL_FACTOR`), and tangent planes (`TangentPlaneCheck`,
  `ARITH_NL_TANGENT_PLANE`).
The strategy stops at the first `BREAK` after a step that added lemmas. If it
adds none, the model check (`NlModel::checkModel`) tries to repair the model;
if that fails, the answer is incomplete (`unknown`).

Before the strategy, `nl-ext-rewrites` simplifies the monomials whose
factors are constants in the equality engine (`ExtTheory::doInferences`,
`EXTT_SIMPLIFY`); at presolve, `nl-ext-initial-sign-lemmas` sends the lemmas
that a monomial is zero when a factor is (`checkInitialRefine`).

The lemmas of the strategy are buffered (`addPendingLemma`), and cvc5 sends
them at last call (`TheoryArith::needsCheckLastEffort`); those of
`ExtTheory` are sent at once.

**State.** cvc5's `ExtTheory` keeps its terms in the SAT context, and the
lemmas it sent, the terms inactive for good, and the monomials whose initial
lemmas were sent, in the user context; the rest is rebuilt at each check or
kept for good (the monomial and constraint databases, the tangent planes'
points, the factoring skolems).

**Node order.** cvc5 iterates over `std::map<Node, _>` and sorts nodes by
id; telos approximates the ids (`NodeOrder`).

**Random.** The flattening check shuffles with cvc5's generator; telos keeps
a generator of its own for it, seeded as cvc5's (cvc5 shares one with the
other users of `Random::getRandom`).

Untrusted: the lemmas are certified when they are sent
(`Telos/Solver/NlLemma.lean`), and a `sat` answer by the model check.
-/

namespace Telos.Solver.Arith.Nl

/-! ## Lemmas -/

/-- What the certificate of a lemma needs (`Telos/Solver/NlLemma.lean`). -/
inductive Info where
  | none
  /-- `(=> (= v 0) (= m 0))`: a factor `v` of `m` is zero. -/
  | zero (v m : Node)
  /-- `(=> antec (r m 0))`: `arith_mult_sign`. -/
  | sign (antec m : Node)
  /-- `(=> exp conc)` comparing magnitudes (`ArithNlCompareProofGenerator`). -/
  | compare
  /-- `arith_mult_tangent` with its arguments. -/
  | tangent (a b av bv : Node) (geq : Bool)
  /-- `arith_mult_pos` or `arith_mult_neg` with `mult` and the bound
  `simple`, which the lemma's explanation states up to rewriting. -/
  | bound (mult simple : Node) (pos : Bool)
  /-- The definition `(= k t)` of a factoring skolem. -/
  | factorDef
  /-- A factoring lemma, of a literal and the skolem of `sum`. -/
  | factor (lit k sum : Node)
  /-- Equal monomials by substitution and normalization. -/
  | flatten
  /-- `EXTT_SIMPLIFY`: a monomial simplified by substitution. -/
  | extt
  /-- `(or eq (not eq))`. -/
  | split (eq : Node)
  deriving Inhabited

structure Lemma where
  id : String
  lem : Node
  info : Info := .none
  deriving Inhabited

/-! ## State -/

/-- `ConstraintInfo`. -/
structure CInfo where
  rhs : Node
  coeff : Option Node
  type : Kind
  deriving Inhabited

/-- The relation kinds in cvc5's enumeration order (`EQUAL` first). -/
def kindRank : Kind → Nat
  | .EQUAL => 0 | .LT => 1 | .LEQ => 2 | .GT => 3 | .GEQ => 4 | .DISTINCT => 5 | _ => 6

/-- `joinKinds`. -/
partial def joinKinds (k1 k2 : Kind) : Option Kind :=
  if kindRank k2 < kindRank k1 then joinKinds k2 k1
  else if k1 == k2 then some k1
  else match k1, k2 with
    | .EQUAL, .LEQ | .EQUAL, .GEQ => some .EQUAL
    | .LT, .LEQ => some .LT
    | .LEQ, .GEQ => some .EQUAL
    | .GT, .GEQ => some .GT
    | _, _ => none

/-- `negateKind`. -/
def negateKind : Kind → Kind
  | .LT => .GEQ | .GT => .LEQ | .LEQ => .GT | .GEQ => .LT
  | .EQUAL => .DISTINCT | .DISTINCT => .EQUAL | k => k

/-- `reverseRelationKind`. -/
def reverseKind : Kind → Kind
  | .LT => .GT | .LEQ => .GEQ | .GEQ => .LEQ | .GT => .LT | k => k

/-- A bound: a key `(x, coeff, rhs)` of the maps `d_ci`, `d_ci_exp`,
`d_ci_max`, with its kind, explanation and maximality. -/
structure Bound where
  coeff : Option Node
  rhs : Node
  kind : Kind
  exp : Node
  max : Bool
  deriving Inhabited

/-- The context of a check, from the engine. -/
structure Ctx where
  order : NodeOrder := {}
  /-- The facts of arithmetic, in order (`facts_begin`). -/
  facts : Array Node := #[]
  /-- Arithmetic's shared terms. -/
  shared : Array Node := #[]
  /-- The representative of a term in the equality engine, if it has it. -/
  rep? : Node → Option Node := fun _ => none
  areEqual : Node → Node → Bool := fun a b => a == b
  /-- The classes of the equality engine (`EqClassesIterator`), each with its
  terms (`EqClassIterator`). -/
  classes : Unit → Array (Array Node) := fun _ => #[]
  /-- The logic is quantified (`nlRlvAssertBounds` and the initial sign lemmas
  are off). -/
  quantified : Bool := false
  /-- Pure integer arithmetic (tangent planes interleaved). -/
  pureInt : Bool := false
  /-- The theory of a term (`Env::theoryOf`) is arithmetic. -/
  isArithTheory : Node → Bool := fun _ => true
  /-- The lemmas sent so far, rewritten (the inference manager's cache). -/
  lemmasSent : Std.HashSet Key := {}
  deriving Inhabited

structure Mark where
  terms : Nat
  inactive : Nat
  deriving Inhabited

structure NlState where
  -- `ExtTheory`, in the SAT context: the terms in order of registration, and
  -- whether active; the ones made inactive, on a trail
  terms : Array Node := #[]
  active : Std.HashMap Key Bool := {}
  inactiveTrail : Array Node := #[]
  marks : Array Mark := #[]
  -- in the user context
  ciInactive : Std.HashSet Key := {}
  extLemmas : Std.HashSet Key := {}
  initRefine : Std.HashSet Key := {}
  -- for good
  mdb : MonomialDb := {}
  /-- The constraint database (`ConstraintDb`): the atoms registered, and
  their bounds by monomial (in node order) and maximal monomials. -/
  cRegistered : Std.HashSet Key := {}
  cInfo : Std.HashMap Key (Array (Node × CInfo)) := {}
  cMax : Std.HashMap Key (Array Node) := {}
  /-- `d_tangent_val_bound`. -/
  tangentVal : Std.HashMap (Nat × Key × Key) Node := {}
  factorSkolems : Std.HashMap Key Node := {}
  /-- `d_mono_diff`. -/
  monoDiff : Std.HashMap (Key × Key) Node := {}
  checkCounter : Nat := 0
  rng : MT := MT.cvc5
  -- of a check
  model : NlModel := {}
  ms : Array Node := #[]
  msVars : Array Node := #[]
  mterms : Array Node := #[]
  tplaneRefine : Std.HashSet Key := {}
  msProc : Std.HashSet Key := {}
  nconstFactor : Std.HashSet Key := {}
  orderVars : Std.HashMap Key Nat := {}
  /-- `d_ci` and its companions: the bounds of each term. -/
  ci : Std.HashMap Key (Array Bound) := {}
  /-- The comparison literals made (`setCompareLit`): their relation and
  sides. -/
  compareLits : Std.HashMap Key (Kind × Node × Node) := {}
  -- the inference manager
  pending : Array Lemma := #[]
  waiting : Array Lemma := #[]
  /-- Lemmas sent at once (`ExtTheory::sendLemma`). -/
  sent : Array Lemma := #[]
  /-- The model is incomplete (`setModelUnsound`). -/
  incomplete : Bool := false
  deriving Inhabited

abbrev NlM := ReaderT Ctx (StateM NlState)

def liftModel (x : ModelM α) : NlM α := do
  let m ← modifyGet fun s => (s.model, { s with model := {} })
  let (a, m) := x.run m
  modify fun s => { s with model := m }
  return a

def rw (t : Node) : NlM Node := return Telos.rewrite t (← read).order
def absValue (n : Node) : NlM Node := liftModel (NlModel.abstractValue n)
def concValue (n : Node) : NlM Node := liftModel (NlModel.concreteValue n)

/-- `nm->mkAnd`: `true`, the literal, or the conjunction. -/
def mkAnd (ls : Array Node) : Node :=
  if ls.isEmpty then Node.mkTrue else if ls.size == 1 then ls[0]! else Node.mkNode .AND ls

/-- `Node::negate`. -/
def negateLit : Node → Node
  | .app (.kind .NOT) #[a] => a
  | l => Node.notNode l

/-- `addPendingLemma`: unless it was sent before (the cache of rewritten
lemmas), as a pending or a waiting lemma. -/
def addPending (l : Lemma) (waiting : Bool := false) : NlM Unit := do
  let r ← rw l.lem
  if (← read).lemmasSent.contains ⟨r⟩ then return
  if waiting then modify fun s => { s with waiting := s.waiting.push l }
  else modify fun s => { s with pending := s.pending.push l }

def hasPending : NlM Bool := return !(← get).pending.isEmpty

/-! ## Context -/

namespace NlState

def push (s : NlState) : NlState :=
  { s with marks := s.marks.push ⟨s.terms.size, s.inactiveTrail.size⟩ }

def pop (s : NlState) : NlState := Id.run do
  let some m := s.marks.back? | return s
  let mut s := { s with marks := s.marks.pop }
  for i in [m.inactive:s.inactiveTrail.size] do
    s := { s with active := s.active.insert ⟨s.inactiveTrail[i]!⟩ true }
  for i in [m.terms:s.terms.size] do
    s := { s with active := s.active.erase ⟨s.terms[i]!⟩ }
  return { s with terms := s.terms.extract 0 m.terms, inactiveTrail := s.inactiveTrail.extract 0 m.inactive }

/-- `NonlinearExtension::preRegisterTerm`: a monomial is registered with the
extended theory (`ExtTheory::registerTerm`). -/
def preRegisterTerm (s : NlState) (n : Node) : NlState :=
  if !isNlMult n || s.active.contains ⟨n⟩ then s
  else { s with terms := s.terms.push n, active := s.active.insert ⟨n⟩ true }

/-- `hasNlTerms`. -/
def hasNlTerms (s : NlState) : Bool := !s.terms.isEmpty

/-- `ExtTheory::getActive`. -/
def getActive (s : NlState) : Array Node :=
  s.terms.filter fun t => s.active.get? ⟨t⟩ == some true && !s.ciInactive.contains ⟨t⟩

/-- `markInactive` (in the SAT context). -/
def markInactive (s : NlState) (t : Node) : NlState :=
  { s with active := s.active.insert ⟨t⟩ false, inactiveTrail := s.inactiveTrail.push t }

end NlState

/-! ## `ExtTheory::doInferences` (`nl-ext-rewrites`) -/

/-- `collectVars`: the leaves of `n` (constants excluded), in cvc5's order. -/
def collectVars (n : Node) : Array Node := Id.run do
  let mut vars := #[]
  let mut visited : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if cur.isConst || visited.contains ⟨cur⟩ then continue
    visited := visited.insert ⟨cur⟩
    if cur.getNumChildren > 0 then work := work ++ cur.getChildren
    else vars := vars.push cur
  return vars

/-- Substitute in `n` (everywhere). -/
partial def substitute (σ : Std.HashMap Key Node) (n : Node) : Node :=
  match σ.get? ⟨n⟩ with
  | some t => t
  | none => match n with
    | .app op cs => .app op (cs.map (substitute σ))
    | n => n

/-- `NlExtTheoryCallback::isExtfReduced`: `sr` (the simplified `t`) is reduced,
with the explanation, minimized for a zero. -/
def isExtfReduced (sr t : Node) (exp : Array Node) : Option (Array Node) :=
  if valOf sr != some 0 then
    if !isNlMult sr then some exp else none
  else Id.run do
    let vars := t.getChildren
    for e in exp do
      let eqs := match e with
        | .app (.kind .EQUAL) #[a, _] => if isArithTerm a then #[e] else #[]
        | .app (.kind .AND) es => es.filter fun e => match e with
          | .app (.kind .EQUAL) #[a, _] => isArithTerm a
          | _ => false
        | _ => #[]
      for eq in eqs do
        let cs := eq.getChildren
        for r in [0, 1] do
          if valOf cs[r]! == some 0 && vars.contains cs[1 - r]! then return some #[eq]
    return some exp

/-- `ExtTheory::doInferences(0)`: the lemmas `exp ⇒ t = sr` for the active
monomials that the constants of the equality engine simplify, sent at once
(`sent`), the monomials made inactive. -/
def extDoInferences : NlM Unit := do
  let terms := (← get).getActive
  if terms.isEmpty then return
  let ctx ← read
  -- the variables of all terms, and their substitution
  let mut vars : Array Node := #[]
  let mut infos : Array (Array Node) := #[]
  for t in terms do
    let vs := collectVars t
    infos := infos.push vs
    for v in vs do if !vars.contains v then vars := vars.push v
  let mut σ : Std.HashMap Key Node := {}
  let mut expc : Std.HashMap Key Node := {}
  let mut useSubs := false
  for v in vars do
    match ctx.rep? v with
    | some r => if r.isConst then
        σ := σ.insert ⟨v⟩ r
        expc := expc.insert ⟨v⟩ (Node.eqNode v r)
        useSubs := true
    | none => pure ()
  if !useSubs then return
  for h : i in [0:terms.size] do
    let t := terms[i]
    let ns := substitute σ t
    if ns == t then continue
    let mut expn : Array Node := #[]
    for v in infos[i]! do
      if let some e := expc.get? ⟨v⟩ then
        if !expn.contains e then expn := expn.push e
    let sr ← rw ns
    if let some exp := isExtfReduced sr t expn then
      modify fun s => s.markInactive t
      let eq := Node.eqNode t sr
      let lem := if exp.isEmpty then eq else Node.mkNode .IMPLIES #[mkAnd exp, eq]
      if !(← get).extLemmas.contains ⟨lem⟩ then
        modify fun s => { s with extLemmas := s.extLemmas.insert ⟨lem⟩,
                                 sent := s.sent.push { id := "EXTT_SIMPLIFY", lem, info := .extt } }

/-! ## `ExtState::init`, `MonomialCheck::init` -/

def one : Node := .const (.integer 1)
def zero : Node := .const (.integer 0)
def negOne : Node := .const (.integer (-1))
/-- `d_order_points`. -/
def orderPoints : Array Node := #[negOne, zero, one]

def register (n : Node) : NlM Unit := do
  let o := (← read).order
  modify fun s => { s with mdb := s.mdb.register o n }

def nlInit (xts : Array Node) : NlM Unit := do
  modify fun s => { s with ms := #[], msVars := #[], mterms := #[], tplaneRefine := {},
                           ci := {}, msProc := {}, nconstFactor := {} }
  for a in xts do
    let _ ← concValue a
    let _ ← absValue a
    if isNlMult a then
      modify fun s => { s with ms := s.ms.push a }
      register a
      for v in (← get).mdb.getVarList a do
        if !(← get).msVars.contains v then modify fun s => { s with msVars := s.msVars.push v }
  register one
  for v in (← get).msVars do
    register v
    let _ ← concValue v
    let _ ← absValue v
  -- `MonomialCheck::init`
  for a in xts do
    if isNlMult a then
      for v in (← get).mdb.getVarList a do
        if !(← absValue v).isConst then modify fun s => { s with nconstFactor := s.nconstFactor.insert ⟨a⟩ }
  for c in orderPoints do
    let _ ← concValue c
    let _ ← absValue c

/-! ## Signs (`MonomialCheck::checkSign`) -/

def sgnOf (n : Node) : Int :=
  match valOf n with
  | some q => if q > 0 then 1 else if q < 0 then -1 else 0
  | none => 0

/-- `checkInitialRefine`: `(=> (= v 0) (= m 0))` for each factor of each new
monomial. -/
def checkInitialRefine (monomials : Array Node) : NlM Unit := do
  for a in monomials do
    if (← get).initRefine.contains ⟨a⟩ then continue
    modify fun s => { s with initRefine := s.initRefine.insert ⟨a⟩ }
    for v in (← get).mdb.getVarList a do
      let prem := Node.eqNode v (zeroOf v)
      let conc := Node.eqNode a (zeroOf a)
      addPending { id := "ARITH_NL_SIGN", lem := Node.mkNode .IMPLIES #[prem, conc], info := .zero v a }

/-- `compareSign`: the sign of `oa` from the signs of the factors of `a` from
`idx` on, with the lemma if the model's sign of `oa` differs. -/
partial def compareSign (oa a : Node) (idx : Nat) (status : Int) (exp : Array Node) : NlM Int := do
  let mvaoa ← absValue oa
  let vla := (← get).mdb.getVarList a
  if idx == vla.size then
    if sgnOf mvaoa != status then
      let z := zeroOf oa
      -- the explanation, in the order of the factors of `oa`
      let mut expo := #[]
      let mut prev : Option Node := none
      for v in oa.getChildren do
        if some v != prev then
          if let some e := exp.find? (fun e => match e with
              | .app (.kind .NOT) #[.app _ #[x, _]] => x == v
              | .app _ #[x, _] => x == v
              | _ => false) then expo := expo.push e
          prev := some v
      let antec := mkAnd expo
      let conc := Node.mkNode (if status > 0 then .GT else .LT) #[oa, z]
      addPending { id := "ARITH_NL_SIGN", lem := Node.mkNode .IMPLIES #[antec, conc], info := .sign antec oa }
    return status
  let av := vla[idx]!
  let z := zeroOf av
  let aexp := (← get).mdb.getExponent a av
  let sgn := sgnOf (← absValue av)
  if sgn == 0 then
    if sgnOf mvaoa != 0 then
      let prem := Node.eqNode av z
      let conc := Node.eqNode oa (zeroOf oa)
      addPending { id := "ARITH_NL_SIGN", lem := Node.mkNode .IMPLIES #[prem, conc], info := .zero av oa }
    return 0
  if aexp % 2 == 0 then
    return ← compareSign oa a (idx + 1) status (exp.push (Node.notNode (Node.eqNode av z)))
  compareSign oa a (idx + 1) (status * sgn) (exp.push (Node.mkNode (if sgn > 0 then .GT else .LT) #[av, z]))

def checkSign : NlM Unit := do
  for a in (← get).ms do
    if (← get).msProc.contains ⟨a⟩ || (← get).nconstFactor.contains ⟨a⟩ then continue
    let s ← compareSign a a 0 1 #[]
    if s == 0 then modify fun st => { st with msProc := st.msProc.insert ⟨a⟩ }

/-! ## Magnitudes (`MonomialCheck::checkMagnitude`) -/

/-- `SortNlModel`: by value (absolute, reversed if asked), then node order. -/
def sortNlModel (xs : Array Node) (concrete absolute reverse : Bool) : NlM (Array Node) := do
  let o := (← read).order
  let mut vals : Array (Node × Node) := #[]
  for x in xs do vals := vals.push (x, ← liftModel (NlModel.value x concrete))
  let cmp := fun (i j : Node × Node) =>
    let ci := i.2; let cj := j.2
    let cv : Int := if i.1 == j.1 then 0
      else if ci.isConst then (if cj.isConst then NlModel.compareValue ci cj absolute else 1)
      else if cj.isConst then -1 else 0
    if cv == 0 then o.lt i.1 j.1 else if reverse then cv > 0 else cv < 0
  return ((vals.toList.mergeSort fun a b => !cmp b a).toArray.map (·.1))

/-- `assignOrderIds`, of the abstract absolute values. -/
def assignOrderIds (vars : Array Node) : NlM (Array Node) := do
  let vars ← sortNlModel vars false true false
  let mut order : Std.HashMap Key Nat := {}
  let mut counter := 0
  let mut idx := 1
  let mut prev : Option Node := none
  for x in vars do
    let v ← absValue x
    if !v.isConst then continue
    if prev != some v then
      let mut go := true
      while go do
        go := false
        if idx < orderPoints.size then
          let vv ← absValue orderPoints[idx]!
          if NlModel.compareValue v vv true ≥ 0 then
            counter := counter + 1
            order := order.insert ⟨orderPoints[idx]!⟩ counter
            prev := some vv
            idx := idx + 1
            go := true
    if prev.isNone || NlModel.compareValue v prev.get! true != 0 then counter := counter + 1
    order := order.insert ⟨x⟩ counter
    prev := some v
  while idx < orderPoints.size do
    counter := counter + 1
    order := order.insert ⟨orderPoints[idx]!⟩ counter
    idx := idx + 1
  modify fun s => { s with orderVars := order }
  return vars

/-- `mkLit(a, b, k, isAbsolute=true)`. -/
def mkAbsLit (k : Kind) (a b : Node) : Node :=
  if k == .EQUAL then
    Node.orNode (Node.eqNode a b) (Node.eqNode a (Node.mkNode .NEG #[b]))
  else
    let za := zeroOf a
    let an := Node.mkNode .GEQ #[a, za]
    let bn := Node.mkNode .GEQ #[b, zeroOf b]
    let na := Node.mkNode .NEG #[a]
    let nb := Node.mkNode .NEG #[b]
    Node.mkNode .ITE #[an, Node.mkNode .ITE #[bn, Node.mkNode k #[a, b], Node.mkNode k #[a, nb]],
      Node.mkNode .ITE #[bn, Node.mkNode k #[na, b], Node.mkNode k #[na, nb]]]

/-- `mkAndNotifyAbsLit`: the types made equal, and the literal recorded. -/
def mkAndNotifyAbsLit (k : Kind) (a b : Node) : NlM Node := do
  let (a, b) :=
    if isRealTerm a != isRealTerm b then
      if !isRealTerm a then (castToReal a, b) else (a, castToReal b)
    else (a, b)
  let lit := mkAbsLit k a b
  modify fun s => { s with compareLits := s.compareLits.insert ⟨lit⟩ (k, a, b) }
  return lit

/-- An exponent map: factor ↦ count (`NodeMultiset`), in node order. -/
abbrev Multiset := Array (Node × Nat)

def msGet (m : Multiset) (v : Node) : Nat := MonomialDb.countIn m v
def msSet (o : NodeOrder) (m : Multiset) (v : Node) (k : Nat) : Multiset :=
  match m.findIdx? (·.1 == v) with
  | some i => m.set! i (v, k)
  | none =>
    let i := (m.findIdx? fun (w, _) => o.lt v w).getD m.size
    m.insertIdx! i (v, k)

/-- The comparisons inferred: status, `oa`, `ob` ↦ lemma (`CompareInferenceMap`). -/
abbrev CmpInfers := Array (Kind × Node × Node × Node)

/-- `compareMonomial` (the recursive one): show `|oa| (status) |ob|` from the
factors of `a` from `ai` and of `b` from `bi`, with the lemma if the model
disagrees; whether it applies. -/
partial def compareMonomialRec (oa a : Node) (ai : Nat) (aproc : Multiset)
    (ob b : Node) (bi : Nat) (bproc : Multiset) (status : Kind) (exp : Array Node) :
    StateT (Array Lemma × CmpInfers) NlM Bool := do
  let o := (← read).order
  let db := (← getThe NlState).mdb
  let vla := db.getVarList a
  let vlb := db.getVarList b
  if ai == vla.size && bi == vlb.size then
    let c ← liftModel (NlModel.compare oa ob false true)
    let modelStatus : Kind := if c < 0 then .LT else if c == 0 then .EQUAL else .GT
    if status != modelStatus then
      let mut exp := exp
      if status == .GT then
        for v in vla do exp := exp.push (Node.notNode (Node.eqNode v (zeroOf v)))
      let conc ← mkAndNotifyAbsLit status oa ob
      let clem := Node.mkNode .IMPLIES #[mkAnd exp, conc]
      modify fun (ls, ci) => (ls.push { id := "ARITH_NL_COMPARISON", lem := clem, info := .compare },
        ci.push (status, oa, ob, clem))
    return true
  let ov := (← getThe NlState).orderVars
  let ovo := (ov.get? ⟨one⟩).getD 0
  -- a's variable
  let mut avM : Option Node := none
  let mut aexp := 0
  let mut avo := 0
  if ai < vla.size then
    let v := vla[ai]!
    aexp := db.getExponent a v - msGet aproc v
    if aexp == 0 then
      return ← compareMonomialRec oa a (ai + 1) aproc ob b bi bproc status exp
    avM := some v
    avo := (ov.get? ⟨v⟩).getD 0
  let mut bvM : Option Node := none
  let mut bexp := 0
  let mut bvo := 0
  if bi < vlb.size then
    let v := vlb[bi]!
    bexp := db.getExponent b v - msGet bproc v
    if bexp == 0 then
      return ← compareMonomialRec oa a ai aproc ob b (bi + 1) bproc status exp
    bvM := some v
    bvo := (ov.get? ⟨v⟩).getD 0
  match avM, bvM with
  | none, some bv =>
    if bvo ≤ ovo then
      let k := if bvo == ovo then Kind.EQUAL else .GT
      let l ← mkAndNotifyAbsLit k (oneOf bv) bv
      return ← compareMonomialRec oa a ai aproc ob b (bi + 1) bproc (if bvo == ovo then status else .GT) (exp.push l)
    return false
  | some av, none =>
    if avo ≥ ovo then
      let k := if avo == ovo then Kind.EQUAL else .GT
      let l ← mkAndNotifyAbsLit k av (oneOf av)
      return ← compareMonomialRec oa a (ai + 1) aproc ob b bi bproc (if avo == ovo then status else .GT) (exp.push l)
    return false
  | some av, some bv =>
    if avo ≥ bvo then
      if bvo < ovo && avo ≥ ovo then
        let k := if avo == ovo then Kind.EQUAL else .GT
        let l ← mkAndNotifyAbsLit k av (oneOf av)
        return ← compareMonomialRec oa a (ai + 1) aproc ob b bi bproc (if avo == ovo then status else .GT) (exp.push l)
      let minExp := min aexp bexp
      let aproc' := msSet o aproc av (msGet aproc av + minExp)
      let bproc' := msSet o bproc bv (msGet bproc bv + minExp)
      let k := if avo == bvo then Kind.EQUAL else .GT
      let l ← mkAndNotifyAbsLit k av bv
      return ← compareMonomialRec oa a ai aproc' ob b bi bproc' (if avo == bvo then status else .GT) (exp.push l)
    if bvo ≤ ovo then
      let k := if bvo == ovo then Kind.EQUAL else .GT
      let l ← mkAndNotifyAbsLit k (oneOf bv) bv
      return ← compareMonomialRec oa a ai aproc ob b (bi + 1) bproc (if bvo == ovo then status else .GT) (exp.push l)
    return false
  | none, none => return false

/-- `compareMonomial`: both directions. -/
def compareMonomial (oa a : Node) (aproc : Multiset) (ob b : Node) (bproc : Multiset) :
    StateT (Array Lemma × CmpInfers) NlM Unit := do
  if ← compareMonomialRec oa a 0 aproc ob b 0 bproc .EQUAL #[] then return
  let _ ← compareMonomialRec ob b 0 bproc oa a 0 aproc .EQUAL #[]

/-- `setMonomialFactor`. -/
def setMonomialFactor (a b : Node) (common : Multiset) : NlM Unit := do
  if (← get).monoDiff.contains (⟨a⟩, ⟨b⟩) then return
  let d := (← get).mdb.remFactor a common
  modify fun s => { s with monoDiff := s.monoDiff.insert (⟨a⟩, ⟨b⟩) d }

/-- `cmp_holds`. -/
partial def cmpHolds (m : Array (Node × Node × Node)) (x y : Node) (visited : Std.HashSet Key) :
    Bool × Std.HashSet Key :=
  if x == y then (true, visited)
  else if visited.contains ⟨x⟩ then (false, visited)
  else Id.run do
    let mut visited := visited.insert ⟨x⟩
    for (x', z, _) in m do
      if x' != x then continue
      let (r, v) := cmpHolds m z y visited
      visited := v
      if r then return (true, visited)
    return (false, visited)

/-- The modes of `checkMagnitude`. -/
inductive MagMode where
  | one | variable | monomial
  deriving BEq

def checkMagnitude (mode : MagMode) : NlM Unit := do
  let o := (← read).order
  if mode == .one then
    let vs ← assignOrderIds (← get).msVars
    modify fun s => { s with msVars := vs }
    -- `sortVariablesByModel`
    for m in (← get).ms do
      let vl ← sortNlModel ((← get).mdb.getVarList m) false true true
      modify fun s => { s with mdb := { s.mdb with vlist := s.mdb.vlist.insert ⟨m⟩ vl } }
  let act : StateT (Array Lemma × CmpInfers) NlM Unit := do
    let ms := (← getThe NlState).ms
    for h : j in [0:ms.size] do
      let a := ms[j]
      let st ← getThe NlState
      if st.msProc.contains ⟨a⟩ || st.nconstFactor.contains ⟨a⟩ then continue
      match mode with
      | .one => compareMonomial a a #[] one one #[]
      | .variable =>
        let mea := st.mdb.getExp a
        for v in st.msVars do
          if !(← concValue v).isConst then continue
          if mea.any (·.1 == v) then
            let ap : Multiset := #[(v, 1)]
            let bp : Multiset := #[(v, 1)]
            setMonomialFactor a v ap
            setMonomialFactor v a bp
            compareMonomial a a ap v v bp
      | .monomial =>
        let mea := st.mdb.getExp a
        for h : k in [j+1:ms.size] do
          let b := ms[k]
          let st ← getThe NlState
          if st.msProc.contains ⟨b⟩ || st.nconstFactor.contains ⟨b⟩ then continue
          let meb := st.mdb.getExp b
          let mut ap : Multiset := #[]
          let mut bp : Multiset := #[]
          for (v, ea) in mea do
            let eb := MonomialDb.countIn meb v
            if eb > 0 then
              ap := msSet o ap v (min ea eb)
              bp := msSet o bp v (min ea eb)
          if !ap.isEmpty then
            setMonomialFactor a b ap
            setMonomialFactor b a bp
          compareMonomial a a ap b b bp
  let ((), (lemmas, infers)) ← act.run (#[], #[])
  -- redundant lemmas: `a > c` when `a > b` and `b > c` were inferred
  let sorted := infers.toList.mergeSort fun (k1, a1, b1, _) (k2, a2, b2, _) =>
    !(kindRank k2 < kindRank k1 || (k2 == k1 && (o.lt a2 a1 || (a2 == a1 && o.lt b2 b1))))
  let byStatus := sorted.toArray
  let mut redundant : Std.HashSet Key := {}
  for (k, oa, ob, lem) in byStatus do
    let m := (byStatus.filter (·.1 == k)).map fun (_, a, b, l) => (a, b, l)
    for (oa', ob', _) in m do
      if oa' != oa || ob' == ob then continue
      let (r, _) := cmpHolds m ob' ob {}
      if r then
        redundant := redundant.insert ⟨lem⟩
        break
  for l in lemmas do
    if !redundant.contains ⟨l.lem⟩ then addPending l

/-! ## Bounds (`MonomialBoundsCheck::checkBounds`) -/

/-- `ConstraintDb::registerConstraint`. -/
def registerConstraint (atom : Node) : NlM Unit := do
  if (← get).cRegistered.contains ⟨atom⟩ then return
  modify fun s => { s with cRegistered := s.cRegistered.insert ⟨atom⟩ }
  let o := (← read).order
  let some msum := MSum.getMonomialSumLit o atom | return
  let mut maxDeg := 0
  let mut all : Array Node := #[]
  let mut maxM : Array Node := #[]
  for (k, _) in msum do
    let some m := k | continue
    all := all.push m
    register m
    let d := (← get).mdb.getDegree m
    if d > maxDeg then
      maxDeg := d
      maxM := #[]
    if d ≥ maxDeg then maxM := maxM.push m
  let mut infos : Array (Node × CInfo) := #[]
  for m in all do
    let (res, coeff, rhs) := MSum.isolate m msum atom.getKind
    if res != 0 then
      let ty := if res == -1 then reverseKind atom.getKind else atom.getKind
      infos := infos.push (m, { rhs, coeff, type := ty })
  modify fun s => { s with cInfo := s.cInfo.insert ⟨atom⟩ infos, cMax := s.cMax.insert ⟨atom⟩ maxM }

/-- `hasNewMonomials`: a monomial in `n` not among `existing`. -/
partial def hasNewMonomials (n : Node) (existing : Array Node) : Bool :=
  if isNlMult n then !existing.contains n
  else n.getChildren.any (hasNewMonomials · existing)

/-- `SortNonlinearDegree`: by degree, then node order. -/
def sortByDegree (ms : Array Node) : NlM (Array Node) := do
  let o := (← read).order
  let db := (← get).mdb
  return (ms.toList.mergeSort fun a b =>
    let da := db.getDegree a; let db' := db.getDegree b
    !(if db' == da then o.lt b a else db' < da)).toArray

/-- The key order of the bounds of a term: by coefficient (null first), then
by right-hand side, in node order. -/
def boundLt (o : NodeOrder) (x y : Bound) : Bool :=
  MSum.keyLt o x.coeff y.coeff || (x.coeff == y.coeff && o.lt x.rhs y.rhs)

def addBound (x : Node) (b : Bound) : NlM Unit := do
  let o := (← read).order
  modify fun s =>
    let bs := (s.ci.get? ⟨x⟩).getD #[]
    let i := (bs.findIdx? fun b' => boundLt o b b').getD bs.size
    { s with ci := s.ci.insert ⟨x⟩ (bs.insertIdx! i b) }

/-- `mkSameType`. -/
def mkSameType (a b : Node) : Node × Node :=
  if isRealTerm a == isRealTerm b then (a, b)
  else if isRealTerm a then (a, castToReal b) else (castToReal a, b)

def checkBounds (asserts falseAsserts : Array Node) : NlM Unit := do
  let ms ← sortByDegree (← get).ms
  modify fun s => { s with ms, mterms := s.mterms ++ s.msVars ++ ms }
  for lit in asserts do
    let (pol, atom) := match lit with
      | .app (.kind .NOT) #[a] => (false, a)
      | a => (true, a)
    registerConstraint atom
    let isFalse := falseAsserts.contains lit
    let some infos := (← get).cInfo.get? ⟨atom⟩ | continue
    let maxM := ((← get).cMax.get? ⟨atom⟩).getD #[]
    for (x, ci) in infos do
      let mut ty := ci.type
      let mut exp := lit
      if !pol then
        if ty == .EQUAL then
          let lhs := MSum.mkCoeffTerm ci.coeff x
          let query := Node.mkNode .GT #[lhs, ci.rhs]
          if (← absValue query) == Node.mkTrue then
            exp := query
            ty := .GT
          else
            exp := Node.mkNode .LT #[lhs, ci.rhs]
            ty := .LT
        else ty := negateKind ty
      let isMax := maxM.contains x
      let bs := ((← get).ci.get? ⟨x⟩).getD #[]
      match bs.findIdx? fun b => b.coeff == ci.coeff && b.rhs == ci.rhs with
      | none => addBound x { coeff := ci.coeff, rhs := ci.rhs, kind := ty, exp, max := isMax }
      | some i =>
        let b := bs[i]!
        let b := { b with max := isMax }
        let b := if ty != b.kind then
            match joinKinds ty b.kind with
            | none => b
            | some jk =>
              if jk != b.kind then
                if jk == ty then { b with kind := ty, exp }
                else { b with kind := jk, exp := Node.mkNode .AND #[b.exp, exp] }
              else b
          else b
        modify fun s => { s with ci := s.ci.insert ⟨x⟩ (bs.set! i b) }
      if isFalse then modify fun s => { s with tplaneRefine := s.tplaneRefine.insert ⟨x⟩ }
  -- reflexive bounds
  for n in (← get).mterms do
    let bs := ((← get).ci.get? ⟨n⟩).getD #[]
    match bs.findIdx? fun b => b.coeff.isNone && b.rhs == n with
    | some i => modify fun s => { s with ci := s.ci.insert ⟨n⟩ (bs.set! i { coeff := none, rhs := n, kind := .EQUAL, exp := Node.mkTrue, max := false }) }
    | none => addBound n { coeff := none, rhs := n, kind := .EQUAL, exp := Node.mkTrue, max := false }
  let ms := (← get).ms
  for x in (← get).mterms do
    let some parents := (← get).mdb.parents x | continue
    let some bs := (← get).ci.get? ⟨x⟩ | continue
    for b in bs do
      if !b.max then continue
      let t := MSum.mkCoeffTerm b.coeff x
      for y in parents do
        let some mult := (← get).mdb.containsDiff? x y | continue
        let mmv ← concValue mult
        if !mmv.isConst then continue
        let sgn := sgnOf mmv
        if sgn == 0 then continue
        let (lhs, rhs) := if b.kind == .EQUAL then mkSameType t b.rhs else (t, b.rhs)
        let inferKind := if sgn == -1 then reverseKind b.kind else b.kind
        let infer := Node.mkNode inferKind #[Node.mkNode .MULT #[mult, lhs], Node.mkNode .MULT #[mult, rhs]]
        let inferMv ← absValue (← rw infer)
        if inferMv == Node.mkFalse then
          let guard := Node.mkNode (if sgn == 1 then .GT else .LT) #[mult, zeroOf mult]
          let exp := Node.mkNode .AND #[guard, b.exp]
          let iblem := Node.mkNode .IMPLIES #[exp, infer]
          let introNew := hasNewMonomials (← rw iblem) ms
          let simple := Node.mkNode b.kind #[lhs, rhs]
          addPending { id := "ARITH_NL_INFER_BOUNDS_NT", lem := iblem, info := .bound mult simple (sgn == 1) } introNew

/-! ## Tangent planes (`TangentPlaneCheck`) -/

def checkTangentPlanes (asWaiting : Bool) : NlM Unit := do
  let o := (← read).order
  let st ← get
  for k in [st.msVars.size:st.mterms.size] do
    let t := (← get).mterms[k]!
    if !(← get).tplaneRefine.contains ⟨t⟩ then continue
    let some cs := (← get).mdb.children t | continue
    let mut dproc : Std.HashSet (Key × Key) := {}
    for tc in cs do
      if tc == oneOf tc then continue
      let some tcDiff := (← get).mdb.containsDiffNl? tc t | continue
      let (a, b) := if o.lt tc tcDiff then (tc, tcDiff) else (tcDiff, tc)
      if dproc.contains (⟨a⟩, ⟨b⟩) then continue
      dproc := dproc.insert (⟨a⟩, ⟨b⟩)
      let avc ← absValue a
      let bvc ← absValue b
      let mut pts0 := #[avc]
      let mut pts1 := #[bvc]
      let tv := (← get).tangentVal
      let prev := tv.contains (0, ⟨a⟩, ⟨b⟩)
      for p in [0:4] do
        let cur := if p ≤ 1 then avc else bvc
        if prev then
          let ptv := (tv.get? (p, ⟨a⟩, ⟨b⟩)).get!
          if cur != ptv then
            let ext ← rw (Node.mkNode (if p == 1 || p == 3 then .GT else .LT) #[cur, ptv])
            if ext == Node.mkTrue then
              for q in [0:2] do
                let other := (tv.get? ((if p ≤ 1 then 2 + q else q), ⟨a⟩, ⟨b⟩)).get!
                if p ≤ 1 then
                  pts0 := pts0.push cur
                  pts1 := pts1.push other
                else
                  pts1 := pts1.push cur
                  pts0 := pts0.push other
        else modify fun s => { s with tangentVal := s.tangentVal.insert (p, ⟨a⟩, ⟨b⟩) cur }
      for p in [0:pts0.size] do
        let av := pts0[p]!
        let bv := pts1[p]!
        let tplane := Node.mkNode .SUB #[Node.mkNode .ADD #[Node.mkNode .MULT #[bv, a], Node.mkNode .MULT #[av, b]],
          Node.mkNode .MULT #[av, bv]]
        for d in [0:2] do
          let b1 := Node.mkNode (if d == 0 then .GEQ else .LEQ) #[b, bv]
          let b2 := Node.mkNode (if d == 0 then .LEQ else .GEQ) #[b, bv]
          let t2 := Node.mkNode .MULT #[a, b]
          let lhs := Node.mkNode (if d == 0 then .LEQ else .GEQ) #[t2, tplane]
          let or1 := Node.mkNode .AND #[Node.mkNode .LEQ #[a, av], b1]
          let or2 := Node.mkNode .AND #[Node.mkNode .GEQ #[a, av], b2]
          let tlem := Node.eqNode lhs (Node.mkNode .OR #[or1, or2])
          addPending { id := "ARITH_NL_TANGENT_PLANE", lem := tlem, info := .tangent a b av bv (d == 1) } asWaiting

/-! ## Factoring (`FactoringCheck`) -/

def realOne : Node := .const (.rational 1)

/-- `getFactorSkolem`: the purification skolem of `n`, with its definition
the first time. -/
def factorSkolem (n : Node) : NlM Node := do
  if let some k := (← get).factorSkolems.get? ⟨n⟩ then return k
  let k := Node.mkPurifySkolem n
  addPending { id := "ARITH_NL_FACTOR", lem := Node.eqNode k n, info := .factorDef }
  modify fun s => { s with factorSkolems := s.factorSkolems.insert ⟨n⟩ k }
  return k

def checkFactoring (asserts falseAsserts : Array Node) : NlM Unit := do
  let o := (← read).order
  for lit in asserts do
    let (pol, atom) := match lit with
      | .app (.kind .NOT) #[a] => (false, a)
      | a => (true, a)
    let _ ← concValue lit
    if !falseAsserts.contains lit then continue
    let some msum := MSum.getMonomialSumLit o atom | continue
    -- factor ↦ the monomials it divides, divided, and the originals; in node order
    let mut f2m : Array (Node × Array Node × Array Node) := #[]
    for (k, c) in msum do
      let some m := k | continue
      if !isNlMult m then continue
      let cs := m.getChildren
      let mut processed : Std.HashSet Key := {}
      for i in [0:cs.size] do
        let f := cs[i]!
        if processed.contains ⟨f⟩ then continue
        processed := processed.insert ⟨f⟩
        -- (the constants of the type of the monomial: cvc5's mixed `1.0` and
        -- coefficient, which telos's typing does not allow)
        let mut children := cs.set! i (oneOf m)
        if let some c := c then children := children.push (mkConstOf m (MSum.coeffVal (some c)))
        let v ← rw (Node.mkNode .MULT children)
        match f2m.findIdx? (·.1 == f) with
        | some j => f2m := f2m.modify j fun (f, vs, os) => (f, vs.push v, os.push m)
        | none =>
          let j := (f2m.findIdx? fun (g, _, _) => o.lt f g).getD f2m.size
          f2m := f2m.insertIdx! j (f, #[v], #[m])
    for (x, vs, os) in f2m do
      let mut vs := vs
      let mut os := os
      if vs.size == 1 then
        if let some c := MSum.get? msum (some x) then
          vs := vs.push (mkConstOf x (MSum.coeffVal c))
          os := os.push x
      if vs.size ≤ 1 then continue
      let sum ← rw (Node.mkNode .ADD vs)
      let sum := match sum with
        | .app (.kind .TO_REAL) #[s] => s
        | s => s
      let kf ← factorSkolem sum
      let mut poly : Array Node := #[Node.mkNode .MULT #[x, kf]]
      for (k, c) in msum do
        let m := k.getD (oneOf x)
        if !(k.isSome && os.contains m) then poly := poly.push (MSum.mkCoeffTerm c m)
      let polyn := if poly.size == 1 then poly[0]! else Node.mkNode .ADD poly
      let concLit ← rw (Node.mkNode atom.getKind #[polyn, zeroOf polyn])
      let concLit := if pol then concLit else negateLit concLit
      let flem := Node.mkNode .OR #[concLit, negateLit lit]
      addPending { id := "ARITH_NL_FACTOR", lem := flem, info := .factor lit kf sum }

/-! ## Flattening (`FlattenMonomialCheck`) -/

/-- `addToFlattenMonMap`. -/
def addToFlattenMap (ns n : Node) (ff : Array (Node × Node)) (repEq : Std.HashMap Key Node) :
    NlM (Array (Node × Node)) := do
  let o := (← read).order
  match ff.find? (·.1 == ns) with
  | none =>
    let i := (ff.findIdx? fun (k, _) => o.lt ns k).getD ff.size
    return ff.insertIdx! i (ns, n)
  | some (_, on) =>
    let ctx ← read
    if ctx.areEqual n on then return ff
    let mut toProcess := #[n, on]
    let mut processed : Std.HashSet Key := {}
    let mut exp : Array Node := #[]
    let mut i := 0
    while i < toProcess.size do
      let v := toProcess[i]!
      i := i + 1
      if processed.contains ⟨v⟩ then continue
      processed := processed.insert ⟨v⟩
      if isNlMult v then
        toProcess := toProcess ++ v.getChildren
        continue
      let vr := (ctx.rep? v).getD v
      if let some r := repEq.get? ⟨vr⟩ then
        if r != v then
          exp := exp.push (Node.eqNode v r)
          toProcess := toProcess.push r
    let conc := Node.eqNode on n
    addPending { id := "ARITH_NL_FLATTEN_MON", lem := Node.mkNode .IMPLIES #[mkAnd exp, conc], info := .flatten }
    return ff

def checkFlatten (mvec : Array Node) : NlM Unit := do
  let ctx ← read
  let o := ctx.order
  let mut as : ArithSubs := {}
  let mut repsProcessed : Std.HashMap Key Node := {}
  let mut ff : Array (Node × Node) := #[]
  for cls in ctx.classes () do
    let some vr := cls[0]? | continue
    if !isArithTerm vr then continue
    let mut base : Array Node := #[]
    let mut nlTerms : Array Node := #[]
    let mut oneT : Option Node := none
    let mut firstBase : Option Node := none
    for n in cls do
      if isNlMult n then nlTerms := nlTerms.push n
      else if n.isConst then
        if valOf n == some 1 then oneT := some n
      else if mvec.contains n then
        if !base.contains n then base := base.push n
        if firstBase.isNone then firstBase := some n
    let mut rep : Option Node := none
    if let some on := oneT then
      rep := some on
      nlTerms := #[]
    let (sh, g) := shuffle nlTerms (← get).rng
    modify fun s => { s with rng := g }
    for n in sh do
      let ns ← rw (as.apply n)
      let fs := if isNlMult ns then ns.getChildren else #[ns]
      if !(fs.any base.contains) then rep := some ns
      ff ← addToFlattenMap ns n ff repsProcessed
    if base.isEmpty then continue
    if rep.isNone then
      if base.size == 1 then continue
      rep := firstBase
    let some r := rep | continue
    let mut tmp : ArithSubs := {}
    for b in base do
      if b != r then tmp := tmp.add b r
    as := { vars := as.vars ++ tmp.vars, subs := as.subs.map tmp.apply ++ tmp.subs }
    repsProcessed := repsProcessed.insert ⟨vr⟩ r
    let mut newEntries : Array (Node × Node) := #[]
    let mut old : Array Node := #[]
    for (k, v) in ff do
      let fnew := tmp.apply k
      if fnew != k then
        newEntries := (newEntries.filter (·.1 != fnew)).push (← rw fnew, v)
        old := old.push k
    ff := ff.filter fun (k, _) => !old.contains k
    let newSorted := newEntries.toList.mergeSort fun (a, _) (b, _) => !o.lt b a
    for (k, v) in newSorted do ff ← addToFlattenMap k v ff repsProcessed

/-! ## The strategy -/

/-- The steps of the strategy, in safe mode. -/
inductive Step where
  | init | sign | mag0 | flatten | mag1 | mag2 | inferBounds | tangentInterleaved
  | flushWaiting | factoring | tangentWaiting | brk
  deriving BEq, Inhabited

/-- `Strategy::initializeStrategy`, for `nl-ext=full` and the defaults. -/
def strategy (pureInt : Bool) : Array Step :=
  #[.init, .brk, .brk, .brk, .sign, .brk, .mag0, .brk, .flatten, .brk, .mag1, .brk, .mag2, .brk,
    .inferBounds] ++ (if pureInt then #[.tangentInterleaved] else #[]) ++
  #[.brk, .brk, .brk, .brk, .flushWaiting, .brk, .factoring, .brk] ++
  (if pureInt then #[] else #[.tangentWaiting]) ++ #[.brk]

/-- `runStrategy`. -/
def runStrategy (assertions falseAsserts xts : Array Node) : NlM Unit := do
  for step in strategy (← read).pureInt do
    match step with
    | .brk => if ← hasPending then return
    | .flushWaiting =>
      modify fun s => { s with pending := s.pending ++ s.waiting, waiting := #[] }
    | .factoring => checkFactoring assertions falseAsserts
    | .init => nlInit xts
    | .flatten => checkFlatten (← get).msVars
    | .inferBounds => checkBounds assertions falseAsserts
    | .mag0 => checkMagnitude .one
    | .mag1 => checkMagnitude .variable
    | .mag2 => checkMagnitude .monomial
    | .sign => checkSign
    | .tangentInterleaved => checkTangentPlanes false
    | .tangentWaiting => checkTangentPlanes true

/-! ## Assertions and the check -/

/-- `BoundInference`: the best lower and upper bounds of the terms of bound
literals, with their literals. -/
structure Bounds where
  lower : Option (Rat × Bool × Node × Node) := none   -- value, strict, bound, origin
  upper : Option (Rat × Bool × Node × Node) := none
  deriving Inhabited

/-- `BoundInference::add` (with `onlyVariables = false`): the literal as a
bound of its term, if it is one. -/
def boundOf (lit : Node) : NlM (Option (Node × Kind × Rat)) := do
  let o := (← read).order
  let tmp ← rw lit
  match tmp with
  | .app (.kind .NOT) #[.app (.kind .EQUAL) _] => return none
  | .const _ => return none
  | _ => pure ()
  let tmp := match tmp with
    | .app (.kind .EQUAL) _ => ((Telos.Arith.normalizeEquality tmp o).map (·.1)).getD tmp
    | t => t
  -- `Comparison::decompose(true)`: `left - right`, its constant moved to the
  -- right, divided by its leading coefficient
  let some cmp := Comparison.parse? tmp | return none
  let rel : Kind := match cmp.kind with
    | .geq => .GEQ | .gt => .GT | .leq => .LEQ | .lt => .LT | .eq => .EQUAL | .distinct => .DISTINCT
  if rel == .DISTINCT then return none
  let p := (Poly.parse cmp.left).sub (Poly.parse cmp.right) o
  let right : Rat := -(((p.terms.find? Poly.isConstantMono).map (·.1)).getD 0)
  let p := p.noConstant
  let lc := p.headCoeff
  if lc == 0 then return none
  let rel := if lc < 0 then reverseKind rel else rel
  let p : Poly := ⟨p.terms.map fun (q, m) => (q / lc, m)⟩
  let lhs := p.node
  let bound := right / lc
  if p.isIntegral then
    match rel with
    | .LEQ => return some (lhs, .LEQ, (bound.floor : Rat))
    | .LT => return some (lhs, .LEQ, ((bound - 1).ceil : Rat))
    | .GT => return some (lhs, .GEQ, ((bound + 1).floor : Rat))
    | .GEQ => return some (lhs, .GEQ, (bound.ceil : Rat))
    | k => return some (lhs, k, (bound.floor : Rat))
  return some (lhs, rel, bound)

/-- `getAssertions`: the facts, with the bound literals replaced by the best
bounds of their terms (`nlRlvAssertBounds`, in quantifier-free logics). -/
def getAssertions : NlM (Array Node) := do
  let ctx ← read
  let mut bounds : Array (Node × Bounds) := #[]
  let mut init : Array Node := #[]
  let o := ctx.order
  for lit in ctx.facts do
    if !ctx.quantified then
      if let some (lhs, rel, v) ← boundOf lit then
        let i := bounds.findIdx? (·.1 == lhs)
        let mut b := (i.map fun i => bounds[i]!.2).getD {}
        let mkB := fun (k : Kind) (val : Rat) => do
          return ← rw (Node.mkNode k #[lhs, mkConstOf lhs val])
        let updLower := fun (b : Bounds) (strict : Bool) => do
          match b.lower with
          | some (lv, _, _, _) =>
            if lv < v then
              let bn ← mkB (if strict then .GT else .GEQ) v
              pure { b with lower := some (v, strict, bn, lit) }
            else if strict && lv == v then
              let bn ← mkB .GT v
              pure { b with lower := some (v, true, bn, lit) }
            else pure b
          | none =>
            let bn ← mkB (if strict then .GT else .GEQ) v
            pure { b with lower := some (v, strict, bn, lit) }
        let updUpper := fun (b : Bounds) (strict : Bool) => do
          match b.upper with
          | some (uv, _, _, _) =>
            if uv > v then
              let bn ← mkB (if strict then .LT else .LEQ) v
              pure { b with upper := some (v, strict, bn, lit) }
            else if strict && uv == v then
              let bn ← mkB .LT v
              pure { b with upper := some (v, true, bn, lit) }
            else pure b
          | none =>
            let bn ← mkB (if strict then .LT else .LEQ) v
            pure { b with upper := some (v, strict, bn, lit) }
        b ← match rel with
          | .LEQ => updUpper b false
          | .LT => updUpper b true
          | .GEQ => updLower b false
          | .GT => updLower b true
          | _ => do let b' ← updLower b false; updUpper b' false
        -- an equality when both bounds meet
        b := match b.lower, b.upper with
          | some (lv, false, _, lo), some (uv, false, _, uo) =>
            if lv == uv then
              let eq := if lo == uo then lo else Node.eqNode lhs (mkConstOf lhs lv)
              let eq := Telos.rewrite eq o
              { lower := some (lv, false, eq, lo), upper := some (uv, false, eq, uo) }
            else b
          | _, _ => b
        bounds := match i with
          | some i => bounds.set! i (lhs, b)
          | none => bounds.push (lhs, b)
        continue
    if !init.contains lit then init := init.push lit
  for (_, b) in bounds do
    if let some (_, _, bn, _) := b.lower then if !init.contains bn then init := init.push bn
    if let some (_, _, bn, _) := b.upper then if !init.contains bn then init := init.push bn
  -- in the order of the facts, then the others
  let mut out : Array Node := #[]
  let mut rest := init
  for lit in ctx.facts do
    if rest.contains lit then
      out := out.push lit
      rest := rest.erase lit
  return out ++ rest

/-- `modelBasedRefinement`: `true` for `sat` (no lemma, the model is
right), `false` for lemmas or an incomplete model. -/
def modelBasedRefinement (termSet : Std.HashSet Key) : NlM Bool := do
  modify fun s => { s with checkCounter := s.checkCounter + 1 }
  let assertions ← getAssertions
  let mut falseAsserts := #[]
  for lit in assertions do
    if (← concValue lit) != Node.mkTrue then falseAsserts := falseAsserts.push lit
  let xts := (← get).terms.filter fun t => termSet.contains ⟨t⟩
  modify fun s => { s with model := s.model.resetCheck }
  let mut complete := true
  if !falseAsserts.isEmpty then
    complete := false
    runStrategy assertions falseAsserts xts
    if (← hasPending) || !(← get).sent.isEmpty then
      modify fun s => { s with waiting := #[] }
      return false
  if !complete then
    if ← liftModel (NlModel.checkModel assertions) then complete := true
    if (← hasPending) || !(← get).sent.isEmpty then
      modify fun s => { s with waiting := #[] }
      return false
  if !complete then
    if !(← get).waiting.isEmpty then
      modify fun s => { s with pending := s.pending ++ s.waiting, waiting := #[] }
      return false
    modify fun s => { s with incomplete := true }
    return false
  modify fun s => { s with waiting := #[] }
  return true

/-- `NonlinearExtension::checkFullEffort`, after `ExtTheory`'s inferences:
the model `vals` (the linear model on the relevant terms `termSet`)
repaired, or lemmas (pending), or an incomplete model. -/
def checkFullEffort (vals : Array (Node × Rat)) (termSet : Std.HashSet Key) :
    NlM (Option (Array (Node × Rat))) := do
  modify fun s => { s with incomplete := false }
  if !(← get).hasNlTerms then return none
  let ctx ← read
  let o := ctx.order
  let valNodes := vals.map fun (n, q) => (n, mkConstOf n q)
  modify fun s => { s with model := NlModel.reset o valNodes }
  let mut pre : Array (Node × Node) := #[]
  for st in ctx.shared do pre := pre.push (st, ← absValue st)
  let sat ← modelBasedRefinement termSet
  if !sat then return none
  let vals' ← liftModel (NlModel.repair vals)
  modify fun s => { s with model := NlModel.reset o (vals'.map fun (n, q) => (n, mkConstOf n q)) }
  -- shared terms that the repair made equal must be split on
  let mut post : Array (Node × Array Node) := #[]
  let mut factorsSplit : Std.HashSet Key := {}
  for st in ctx.shared do
    let v ← absValue st
    match post.findIdx? (·.1 == v) with
    | some i => post := post.modify i fun (v, ts) => (v, ts.push st)
    | none => post := post.push (v, #[st])
    if isNlMult st then
      for f in st.getChildren do
        if !(vals'.any (·.1 == f)) && !factorsSplit.contains ⟨f⟩ then
          factorsSplit := factorsSplit.insert ⟨f⟩
          let eq := Node.eqNode f (zeroOf f)
          addPending { id := "ARITH_NL_SHARED_TERM_FACTOR_SPLIT", lem := Node.orNode eq (Node.notNode eq), info := .split eq }
  for (_, ts) in post do
    let mut cv : Option Node := none
    for st in ts do
      let stv := ((pre.find? (·.1 == st)).map (·.2)).getD st
      match cv with
      | none => cv := some stv
      | some c =>
        if stv != c then
          let eq := Node.eqNode st ts[0]!
          addPending { id := "ARITH_NL_SHARED_TERM_SPLIT", lem := Node.orNode eq (Node.notNode eq), info := .split eq }
  return some vals'

/-- `NonlinearExtension::presolve`: the initial sign lemmas of the monomials
preregistered. -/
def presolve : NlM Unit := do
  if (← read).quantified then return
  let ms := (← get).terms.filter isNlMult
  if ms.isEmpty then return
  for m in ms do register m
  checkInitialRefine ms

end Telos.Solver.Arith.Nl
