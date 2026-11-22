import Telos.Rewriter.Rewrite
import Telos.Core.Node.Print
import Telos.Solver.Theory.Arith.Cert

/-!
# The linear arithmetic solver

A port of cvc5's `TheoryArithPrivate` (`src/theory/arith/linear/
theory_arith_private.cpp`), in the configuration of safe mode with proofs
(`docs/theory-engine-plan.md`, Stage 7). So far: preregistration
(`preRegisterTerm`, `setupAtom`, `setupPolynomial`), the unate lemmas of
`presolve` (`ConstraintDatabase::outputUnate*Lemmas`), the assertion of facts
(`constraintFromFactQueue`, `assertionCases`, `Assert*`), `postCheck` with the
dual simplex (`Simplex.lean`), unate propagation, disequality splits, the
propagations of the constraint database, and the explanations.

Not yet: the congruence manager, integers (branch and bound, cuts, the Diophantine solver).

The solver's lemmas are `Output`s, which the engine turns into events and
clauses.
-/

namespace Telos.Solver.Arith

open State

/-- An error that makes the answer `unknown` (a nonlinear term, say). -/
def unsupported (why : String) : ArithM Unit :=
  modify fun s => if s.unsupported.isSome then s else { s with unsupported := some why }

def isSetup (n : Node) : ArithM Bool := return (← get).setupNodes.contains ⟨n⟩
def markSetup (n : Node) : ArithM Unit := modify fun s => { s with setupNodes := s.setupNodes.insert ⟨n⟩ }

/-- `requestArithVar`: a new arith variable for `n`, with its column and its
constraint map. -/
def requestArithVar (n : Node) (aux integral : Bool) : ArithM Nat := do
  let x ← modifyGet fun s => let (s, x) := s.allocate n aux integral; (x, s)
  modify fun s => { s with tableau := s.tableau.increaseSizeTo s.numVars }
  modify fun s => s.addVariableDb
  return x

/-- `setupVariable`. -/
def setupVariable (n : Node) : ArithM Unit := do
  let _ ← requestArithVar n false (Telos.Arith.isInt n)
  markSetup n

/-- `setupVariableList`: the variables of a monomial's variable part. A
product of several variables is nonlinear, which a linear logic rejects. -/
def setupVariableList (m : Node) : ArithM Unit := do
  match m with
  | .app (.kind .MULT) cs =>
    for v in cs do
      if !(← isSetup v) then setupVariable v
    unsupported s!"a nonlinear term: {m.toSmtLib}"
  | _ => if !(← isSetup m) then setupVariable m

/-- `LinearEqualityModule::computeRowValue`. -/
def computeRowValue (s : State) (x : Nat) (useSafe : Bool) : DeltaRational :=
  (s.tableau.basicRowEntries x).foldl (fun sum id =>
    let e := s.tableau.entry id
    if e.col == x then sum else sum + s.getAssignmentSafe e.col useSafe * e.coeff) 0

/-- `setupBasicValue`. -/
def setupBasicValue (x : Nat) : ArithM Unit :=
  modify fun s => s.setAssignment2 x (computeRowValue s x true) (computeRowValue s x false)

/-- `notifySharedTerm`: the variables of a shared term are set up (`to_real`
dropped). -/
def notifySharedTerm (n : Node) : ArithM Unit := do
  let n := match n with
    | .app (.kind .TO_REAL) #[a] => a
    | n => n
  if constVal? n |>.isNone then
    if !(← isSetup n) then
      for (_, m) in (Poly.parse n).terms do
        if m != Poly.one && !(← isSetup m) then setupVariableList m

/-- `setupPolynomial`: the variables of the monomials, and for a sum, its slack
variable and its row. -/
def setupPolynomial (p : Poly) : ArithM Unit := do
  for (_, m) in p.terms do
    if !(← isSetup m) then setupVariableList m
  if p.terms.size > 1 then
    let s ← get
    let vars := p.terms.map fun (_, m) => (s.asArithVar? m).get!
    let coeffs := p.terms.map (·.1)
    let slack ← requestArithVar p.node true p.isIntegral
    modify fun s => { s with tableau := s.tableau.addRow slack coeffs vars }
    setupBasicValue slack
    trackRowIndex ((← get).tableau.basicToRowIndex slack)
    markSetup p.node

/-- The normal form of an atom for the solver: an equality is normalized
(`rewriter::normalizeEquality`), an inequality is already. -/
def normalAtom (atom : Node) : Node :=
  match atom with
  | .app (.kind .EQUAL) _ => ((Telos.Arith.normalizeEquality atom).map (·.1)).getD atom
  | _ => atom


/-- `outputTrustedLemma`: a lemma goes out unless it was sent before (the
inference manager's cache of the rewritten lemmas, `cacheLemma`); whether it
did. -/
def sendLemma (id : String) (lem : Node) (cert : Option LinCert := none) : ArithM Bool := do
  let r := Telos.rewrite lem (← get).opts.order
  if (← get).lemmasSent.contains ⟨r⟩ then return false
  modify fun s => { s with lemmasSent := s.lemmasSent.insert ⟨r⟩, outputs := s.outputs.push (.lemma id lem cert) }
  return true

/-- `setupAtom`. -/
def setupAtom (atom : Node) : ArithM Unit := do
  let natom := normalAtom atom
  let some cmp := Comparison.parse? natom | unsupported s!"an atom not in normal form: {atom.toSmtLib}"
  let nvp := cmp.normalizedVariablePart (← get).opts.order
  if !(← isSetup nvp.node) then setupPolynomial nvp
  if (← get).unsupported.isSome then return
  let _ ← ageOf atom
  let _ ← ageOf (Node.notNode atom)
  -- the atom and its negation (`addLiteral`), numbered among the nodes built
  -- during solving
  modify fun s =>
    let o := s.opts.order
    { s with opts := { s.opts with order := { o with fresh := o.numberFresh o.fresh (Node.notNode atom) } } }
  let c ← modifyGet fun s => let (s, c) := s.addLiteral atom natom; (c, s)
  markSetup atom
  let lit := ((← get).constraint c).literal.get!
  if lit != atom then
    let _ ← sendLemma "ARITH_EQUIV_ATOM" (Node.eqNode lit atom)

/-- `isRelationOperator`. -/
def isRelation : Node → Bool
  | .app (.kind k) _ => k == .GEQ || k == .GT || k == .LEQ || k == .LT || k == .EQUAL
  | _ => false

/-- `preRegisterTerm`. -/
def preRegisterTerm (n : Node) : ArithM Unit := do
  if !isRelation n then return
  if !(← isSetup n) then setupAtom n
  if (← get).unsupported.isSome then return
  let some c := (← get).lookup n | return
  if !((← get).constraint c).canBePropagated then modify fun s => s.setPreregistered c

/-! ## The unate lemmas of `presolve` -/

/-- The certificate of a lemma `(or l₁ … lₙ)`. -/
def orCert : Node → Option LinCert
  | .app (.kind .OR) cs => clauseCert cs
  | _ => none

/-- `proveOr`: `(or la lb)`, its disjuncts ordered by node id: by the order of
the input and its rewriting (`NodeOrder`), then, for the nodes created later,
by first occurrence (`ageOf`). -/
def proveOr (a b : Nat) : ArithM Node := do
  let s ← get
  let la := (s.constraint a).literal.get!
  let lb := (s.constraint b).literal.get!
  let ia ← ageOf la
  let ib ← ageOf lb
  let key (l : Node) (age : Nat) : Nat × Nat := match s.opts.order.id? l with
    | some i => (0, i)
    | none => (1, age)
  let (ka, kb) := (key la ia, key lb ib)
  let lt := ka.1 < kb.1 || (ka.1 == kb.1 && ka.2 < kb.2)
  return if lt then .app (.kind .OR) #[la, lb] else .app (.kind .OR) #[lb, la]

/-- `implies`: `a ⇒ b`. -/
def implies (a b : Nat) : ArithM Node := do proveOr ((← get).constraint a).negation b

/-- `mutuallyExclusive`. -/
def mutuallyExclusive (a b : Nat) : ArithM Node := do
  let s ← get
  proveOr (s.constraint a).negation (s.constraint b).negation

/-- `Constraint::split`: `(or (<= l r) (>= l r))` for the equality's literal. -/
def split (c : Nat) : ArithM Node := do
  let s ← get
  let k := s.constraint c
  let eq := if k.isEquality then c else k.negation
  let diseq := (s.constraint eq).negation
  let some (.app (.kind .EQUAL) #[l, r]) := (s.constraint eq).literal | return Node.mkTrue
  let mark := fun (k : Constraint) => { k with split := true }
  modify fun s => { s with constraints := (s.constraints.modify eq mark).modify diseq mark }
  return .app (.kind .OR) #[.app (.kind .LEQ) #[l, r], .app (.kind .GEQ) #[l, r]]

def hasLiteral (c : Nat) : ArithM Bool := return ((← get).constraint c).literal.isSome

/-- `outputUnateInequalityLemmas` of a variable: each upper bound with a
literal implies the next one. -/
def unateInequalityLemmas (x : Nat) : ArithM (Array Node) := do
  let mut out := #[]
  let mut prev : Option Nat := none
  for (_, vc) in (← get).scm[x]! do
    if let some ub := vc.ub then
      if ← hasLiteral ub then
        if let some p := prev then out := out.push (← implies p ub)
        prev := some ub
  return out

/-- `outputUnateEqualityLemmas` of a variable. -/
def unateEqualityLemmas (x : Nat) : ArithM (Array Node) := do
  let mut eqs := #[]
  for (_, vc) in (← get).scm[x]! do
    if let some eq := vc.eq then
      if ← hasLiteral eq then eqs := eqs.push eq
  let mut out := #[]
  for i in [0:eqs.size] do
    for j in [i+1:eqs.size] do
      out := out.push (← mutuallyExclusive eqs[i]! eqs[j]!)
  for eq in eqs do
    let s ← get
    let k := s.constraint eq
    let vc := (s.scmAt k.var k.value).get!
    let hasLB := match vc.lb with
      | some c => (s.constraint c).literal.isSome
      | none => false
    let hasUB := match vc.ub with
      | some c => (s.constraint c).literal.isSome
      | none => false
    let lb := if hasLB then vc.lb else s.getStrictlyWeakerLowerBound eq true false
    let ub := if hasUB then vc.ub else s.getStrictlyWeakerUpperBound eq true false
    if hasUB && hasLB && !k.split then out := out.push (← split eq)
    if let some lb := lb then out := out.push (← implies eq lb)
    if let some ub := ub then out := out.push (← implies eq ub)
  return out

/-- `presolve`, with `arithUnateLemmaMode=ALL`: the inequality lemmas of each
variable, then the equality lemmas. -/
def presolve : ArithM Unit := do
  let n := (← get).numVars
  let mut lemmas := #[]
  for x in [0:n] do lemmas := lemmas ++ (← unateInequalityLemmas x)
  for x in [0:n] do lemmas := lemmas ++ (← unateEqualityLemmas x)
  for l in lemmas do let _ ← sendLemma "ARITH_UNATE" l (orCert (Telos.rewrite l (← get).opts.order))

/-! ## Explanations -/

/-- `externalExplain`: the witnesses of the constraints asserted before
`order` (all if `none`) that `c` follows from, in the order of its proof
(each rule's antecedents from the last). -/
partial def explainInto (s : State) (c : Nat) (order : Option Nat) (acc : Array Node) : Array Node :=
  let k := s.constraint c
  let before := match order with
    | none => k.assertedToTheTheory
    | some o => k.assertedBefore o
  if before then acc.push k.witness.get!
  else if s.proofType? c == some .equalityEngine then acc.push k.literal.get!
  else match s.rule c with
    | some r => Id.run do
      let mut acc := acc
      let mut p := r.antecedentEnd
      repeat
        match p with
        | some i =>
          match s.antecedents[i]! with
          | some a =>
            acc := explainInto s a order acc
            p := if i == 0 then none else some (i - 1)
          | none => break
        | none => break
      return acc
    | none => acc

/-- `mkAndFromBuilder`. -/
def mkAndOf (ns : Array Node) : Node :=
  if ns.isEmpty then Node.mkTrue else if ns.size == 1 then ns[0]! else .app (.kind .AND) ns

/-- `externalExplainConflict`: the explanations of `c` and of its negation. -/
def explainConflict (s : State) (c : Nat) : Node :=
  mkAndOf (explainInto s (s.constraint c).negation none (explainInto s c none #[]))

/-- `TheoryArithPrivate::explain` of a propagated literal
(`externalExplainForPropagation`). -/
def explain (lit : Node) : ArithM (Array Node) := do
  let s ← get
  let some c := s.lookup lit | return #[]
  return explainInto s c (s.constraint c).assertionOrder #[]

/-- The certificate of the explanation of a propagated literal (see `explain`):
it refutes the explanation with the negation of the literal. -/
def explainCert (lit : Node) : ArithM (Option LinCert) := do
  return propagationCert (← get) lit

/-! ## Asserting facts -/

/-- `anyConflict`. -/
def anyConflict : ArithM Bool := return !(← get).conflicts.isEmpty || (← get).blackBox.isSome

def isTrueC (c : Nat) : ArithM Bool := return (← get).isTrue c
def negationOfC (c : Nat) : ArithM Nat := return ((← get).constraint c).negation
def vcOf (c : Nat) : ArithM ValueCollection := do
  let s ← get
  let k := s.constraint c
  return (s.scmAt k.var k.value).get!

/-- `ensureConstraint`. -/
def ensureConstraint (c : Nat) (t : CType) : ArithM Nat := do
  let vc ← vcOf c
  match vc.get t with
  | some d => return d
  | none =>
    let k := (← get).constraint c
    modifyGet fun s => let (s, d) := s.getConstraint k.var t k.value; (d, s)

def pushPropList (c : Option Nat) : ArithM Unit := modify fun s => { s with propList := s.propList.push c }

/-- The end of `AssertLower`/`AssertUpper`/`AssertEquality`: the bound is
recorded as updated, and the variable updated (nonbasic) or signaled (basic). -/
def afterBound (x : Nat) (violates : State → Bool) (c : DeltaRational) : ArithM Unit := do
  modify fun s => { s with updatedBounds := s.updatedBounds.add x }
  let s ← get
  if !s.tableau.isBasic x then
    if violates s then update x c
  else signalVariable x

/-- An integer variable whose bounds are now equal, for the Diophantine solver
(`d_constantIntegerVariables`). -/
def pushConstantInteger (x : Nat) : ArithM Unit := do
  if (← get).isInteger x then modify fun s => { s with constantIntegers := s.constantIntegers.push x }

/-- `AssertLower`. -/
def assertLower (c : Nat) : ArithM Bool := do
  let s ← get
  let k := s.constraint c
  let x := k.var
  if s.cmpToLowerBound x k.value ≤ 0 then return false
  let cmpToUB := s.cmpToUpperBound x k.value
  if cmpToUB > 0 then
    impliedByUnate k.negation (s.var x).ub.get!
    raiseConflict c "ARITH_CONF_LOWER"
    return true
  else if cmpToUB == 0 then
    pushConstantInteger x
    let ub := (s.var x).ub.get!
    let vc ← vcOf c
    if let some eq := vc.eq then
      let diseq := vc.diseq.get!
      let triConflict ← isTrueC diseq
      if !(← isTrueC eq) then
        impliedByTrichotomy eq c ub
        modify fun s => s.tryToPropagate eq
      if triConflict then
        raiseConflict eq "ARITH_CONF_TRICHOTOMY"
        return true
  else
    let vc ← vcOf c
    if let some diseq := vc.diseq then
      if ← isTrueC diseq then
        let ub ← ensureConstraint c .upperBound
        let negUb ← negationOfC ub
        let ubInConflict ← isTrueC ub
        let learn := !(← isTrueC negUb)
        if learn then
          impliedByTrichotomy negUb c diseq
          modify fun s => s.tryToPropagate negUb
        if ubInConflict then
          raiseConflict ub "ARITH_CONF_TRICHOTOMY"
          return true
        else if learn then modify fun s => { s with learnedBounds := s.learnedBounds.push negUb }
  pushPropList (some c)
  pushPropList ((← get).var x).lb
  modify fun s => s.setLowerBoundConstraint c
  afterBound x (fun s => s.assignment x < k.value) k.value
  return false

/-- `AssertUpper`. -/
def assertUpper (c : Nat) : ArithM Bool := do
  let s ← get
  let k := s.constraint c
  let x := k.var
  if s.cmpToUpperBound x k.value ≥ 0 then return false
  let cmpToLB := s.cmpToLowerBound x k.value
  if cmpToLB < 0 then
    impliedByUnate k.negation (s.var x).lb.get!
    raiseConflict c "ARITH_CONF_UPPER"
    return true
  else if cmpToLB == 0 then
    pushConstantInteger x
    let lb := (s.var x).lb.get!
    let vc ← vcOf c
    if let some diseq := vc.diseq then
      let eq := vc.eq.get!
      let triConflict ← isTrueC diseq
      if !(← isTrueC eq) then
        impliedByTrichotomy eq c lb
        modify fun s => s.tryToPropagate eq
      if triConflict then
        raiseConflict eq "ARITH_CONF_TRICHOTOMY"
        return true
  else
    let vc ← vcOf c
    if let some diseq := vc.diseq then
      if ← isTrueC diseq then
        let lb ← ensureConstraint c .lowerBound
        let negLb ← negationOfC lb
        let lbInConflict ← isTrueC lb
        let learn := !(← isTrueC negLb)
        if learn then
          impliedByTrichotomy negLb c diseq
          modify fun s => s.tryToPropagate negLb
        if lbInConflict then
          raiseConflict lb "ARITH_CONF_TRICHOTOMY"
          return true
        else if learn then modify fun s => { s with learnedBounds := s.learnedBounds.push negLb }
  pushPropList (some c)
  pushPropList ((← get).var x).ub
  modify fun s => s.setUpperBoundConstraint c
  afterBound x (fun s => s.assignment x > k.value) k.value
  return false

/-- `AssertEquality`. -/
def assertEquality (c : Nat) : ArithM Bool := do
  let s ← get
  let k := s.constraint c
  let x := k.var
  let cmpToLB := s.cmpToLowerBound x k.value
  let cmpToUB := s.cmpToUpperBound x k.value
  if cmpToUB ≥ 0 && cmpToLB ≤ 0 then return false
  if cmpToUB > 0 || cmpToLB < 0 then
    let cb := if cmpToUB > 0 then (s.var x).ub.get! else (s.var x).lb.get!
    impliedByUnate k.negation cb
    raiseConflict c "ARITH_CONF_EQ"
    return true
  pushConstantInteger x
  pushPropList (some c)
  pushPropList (s.var x).lb
  pushPropList (s.var x).ub
  modify fun s => s.setUpperBoundConstraint c
  modify fun s => s.setLowerBoundConstraint c
  afterBound x (fun s => s.assignment x != k.value) k.value
  return false

/-- `AssertDisequality`. -/
def assertDisequality (c : Nat) : ArithM Bool := do
  let vc ← vcOf c
  if let (some lb, some ub) := (vc.lb, vc.ub) then
    if (← isTrueC lb) && (← isTrueC ub) then
      impliedByTrichotomy (← negationOfC c) lb ub
      raiseConflict c "ARITH_CONF_TRICHOTOMY"
      return true
  if let some lb := vc.lb then
    if ← isTrueC lb then
      let ub ← ensureConstraint c .upperBound
      let negUb ← negationOfC ub
      if !(← isTrueC negUb) then
        impliedByTrichotomy negUb c lb
        modify fun s => (s.tryToPropagate negUb)
        modify fun s => { s with learnedBounds := s.learnedBounds.push negUb }
  let vc ← vcOf c
  if let some ub := vc.ub then
    if ← isTrueC ub then
      let lb ← ensureConstraint c .lowerBound
      let negLb ← negationOfC lb
      if !(← isTrueC negLb) then
        impliedByTrichotomy negLb c ub
        modify fun s => (s.tryToPropagate negLb)
        modify fun s => { s with learnedBounds := s.learnedBounds.push negLb }
  let s ← get
  let k := s.constraint c
  if !k.split && k.value == s.assignment k.var then
    let lem ← split c
    let _ ← sendLemma "ARITH_SPLIT_DEQ" lem (orCert (Telos.rewrite lem (← get).opts.order))
    return false
  if s.cmpToLowerBound k.var k.value < 0 || s.cmpToUpperBound k.var k.value > 0 then return false
  if !k.split then modify fun s => { s with diseqQueue := s.diseqQueue.push c, deltaIsSafe := false }
  return false

/-- `assertionCases`: an integer's strict bound is tightened first. -/
def assertionCases (c : Nat) : ArithM Bool := do
  let s ← get
  let k := s.constraint c
  match k.type with
  | .upperBound =>
    if s.isInteger k.var && k.isStrictUpperBound then
      let fl ← modifyGet fun s => let (s, d) := s.getConstraint k.var .upperBound (k.value.floor : Rat); (d, s)
      if !(← isTrueC fl) then
        let inConflict := (← get).negationHasProof fl
        impliedByIntTighten fl c
        modify fun s => s.tryToPropagate fl
        if inConflict then
          raiseConflict fl "ARITH_TIGHTEN_FLOOR"
          return true
      assertUpper fl
    else assertUpper c
  | .lowerBound =>
    if s.isInteger k.var && k.isStrictLowerBound then
      let ce ← modifyGet fun s => let (s, d) := s.getConstraint k.var .lowerBound (k.value.ceiling : Rat); (d, s)
      if !(← isTrueC ce) then
        let inConflict := (← get).negationHasProof ce
        impliedByIntTighten ce c
        modify fun s => s.tryToPropagate ce
        if inConflict then
          raiseConflict ce "ARITH_TIGHTEN_CEIL"
          return true
      assertLower ce
    else assertLower c
  | .equality => assertEquality c
  | .disequality => assertDisequality c

/-- `constraintFromFactQueue`: the constraint of an asserted literal, set
asserted, and an assumption unless it already has a proof. -/
def constraintFromFactQueue (fact : Node) : ArithM (Option Nat) := do
  let c ← match (← get).lookup fact with
    | some c => pure (some c)
    | none =>
      -- an equality not set up (or its negation), by its rewrite
      let (isDistinct, eq) := match fact with
        | .app (.kind .NOT) #[a] => (true, a)
        | a => (false, a)
      let reEq := Telos.rewrite eq (← get).opts.order
      if reEq == Node.mkTrue || reEq == Node.mkFalse then
        -- a false one (`(not true)`, or `false`) is a conflict by itself
        -- (`raiseBlackBoxConflict`), refuted by its Farkas combination; a true
        -- one is ignored
        if (reEq == Node.mkTrue) == isDistinct then
          let cert := ([#[(fact, (1 : Rat))], #[(fact, -1)]].find? (checkFarkas #[fact])).map LinCert.farkas
          modify fun s => { s with blackBox := s.blackBox <|> some (fact, cert) }
        return none
      if !(← isSetup reEq) then setupAtom reEq
      pure ((← get).lookup (if isDistinct then Node.notNode reEq else reEq))
  let some c := c | return none
  let s ← get
  if (s.constraint c).assertedToTheTheory then return none
  let inConflict := s.negationHasProof c
  modify fun s => s.setAssertedToTheTheory c fact
  if !(← get).hasProof c then modify fun s => s.setAssumption c
  if inConflict then
    raiseConflict (← negationOfC c) "ARITH_CONF_FACT_QUEUE"
    return none
  return some c

/-- `TheoryArith::preNotifyFact`. -/
def assertFact (fact : Node) : ArithM Unit := do
  if (← get).unsupported.isSome then return
  if let some c ← constraintFromFactQueue fact then
    let _ ← assertionCases c

/-- `preCheck`. -/
def preCheck (newFacts : Bool) : ArithM Unit :=
  modify fun s => { s with newFacts, previousStatus := s.qflraStatus,
                           qflraStatus := if newFacts then .unknown else s.qflraStatus,
                           hasDoneWorkSinceCut := s.hasDoneWorkSinceCut || newFacts }

/-! ## `postCheck` -/

/-- `revertOutOfConflict`. -/
def revertOutOfConflict : ArithM Unit :=
  modify fun s => { s.revertAssignmentChanges with updatedBounds := s.updatedBounds.purge,
                                                   propList := #[], propListHead := 0 }

/-- `outputConflicts`: each conflict's explanation. -/
def outputConflicts : ArithM Unit := do
  let s ← get
  for (c, id) in s.conflicts do
    modify fun s => { s with outputs := s.outputs.push (.conflict id (explainConflict s c) (conflictCert s c)) }
  if let some (bb, cert) := s.blackBox then
    modify fun s => { s with outputs := s.outputs.push (.conflict "ARITH_BLACK_BOX" bb cert) }

/-- `handleUnateProp`. -/
def handleUnateProp (ant cons : Nat) : ArithM Bool := do
  let s ← get
  if s.negationHasProof cons then
    impliedByUnate cons ant
    raiseConflict cons "ARITH_CONF_UNATE_PROP"
    return true
  else if !s.isTrue cons then
    impliedByUnate cons ant
    modify fun s => s.tryToPropagate cons
    return false
  else return false

/-- `unatePropLowerBound`: the lower bounds and disequalities below `curr`, down
to the previous bound. -/
def unatePropLowerBound (curr : Nat) (prev : Option Nat) : ArithM Unit := do
  let s ← get
  let k := s.constraint curr
  let m := s.scm[k.var]!
  let mut i := s.scmPos curr
  while i > 0 do
    i := i - 1
    let vc := m[i]!.2
    if let some p := prev then
      if vc.get ((← get).constraint p).type == some p then break
    if let some lb := vc.lb then
      if ← handleUnateProp curr lb then return
    if let some d := vc.diseq then
      if ← handleUnateProp curr d then return

/-- `unatePropUpperBound`. -/
def unatePropUpperBound (curr : Nat) (prev : Option Nat) : ArithM Unit := do
  let s ← get
  let k := s.constraint curr
  let m := s.scm[k.var]!
  for i in [s.scmPos curr + 1:m.size] do
    let vc := m[i]!.2
    if let some p := prev then
      if vc.get ((← get).constraint p).type == some p then break
    if let some ub := vc.ub then
      if ← handleUnateProp curr ub then return
    if let some d := vc.diseq then
      if ← handleUnateProp curr d then return

/-- `unatePropEquality`. -/
def unatePropEquality (curr : Nat) (prevLB prevUB : Option Nat) : ArithM Unit := do
  let s ← get
  let k := s.constraint curr
  let m := s.scm[k.var]!
  let pos := s.scmPos curr
  let last := match prevUB with
    | some u => s.scmPos u
    | none => m.size
  let mut i := match prevLB with
    | some l => let p := s.scmPos l; if p != pos then p + 1 else p
    | none => 0
  while i < pos do
    let vc := m[i]!.2
    if let some lb := vc.lb then
      if ← handleUnateProp curr lb then return
    if let some d := vc.diseq then
      if ← handleUnateProp curr d then return
    i := i + 1
  if prevUB.isNone || i != last then i := i + 1
  while i < last do
    let vc := m[i]!.2
    if let some ub := vc.ub then
      if ← handleUnateProp curr ub then return
    if let some d := vc.diseq then
      if ← handleUnateProp curr d then return
    i := i + 1

def popPropList : ArithM (Option Nat) := do
  let s ← get
  let c := s.propList[s.propListHead]!
  modify fun s => { s with propListHead := s.propListHead + 1 }
  return c

/-- `solveRealRelaxation` (the dual simplex only: `useApprox` is off). -/
def solveRealRelaxation (full : Bool) : ArithM Bool := do
  modify fun s => { s with enqueueingBoundCounts := false }
  processBoundsQueueTracking
  modify fun s => { s with areTracking := true }
  let st ← dualFindModel full  -- `noPivotLimit`: full effort (`restrictedPivots`)
  modify fun s => { s with qflraStatus := st }
  -- `solveRelaxationOrPanic`: a second pass when unknown
  if (← get).qflraStatus == .unknown then
    let st ← dualFindModel false
    modify fun s => { s with qflraStatus := st }
  if full && (← get).qflraStatus == .unknown then
    unsupported "the simplex does not finish at full effort"
  modify fun s => { s with areTracking := false, enqueueingBoundCounts := true }
  return false

/-- `splitDisequalities`. -/
def splitDisequalities : ArithM Bool := do
  let mut split_ := false
  let mut save := #[]
  while (← get).diseqQueueHead < (← get).diseqQueue.size do
    let s ← get
    let front := s.diseqQueue[s.diseqQueueHead]!
    modify fun s => { s with diseqQueueHead := s.diseqQueueHead + 1 }
    let k := s.constraint front
    if k.split then continue
    if s.assignment k.var == k.value then
      let lem ← split front
      let _ ← sendLemma "ARITH_SPLIT_DEQ" lem (orCert (Telos.rewrite lem (← get).opts.order))
      split_ := true
    else if s.cmpToLowerBound k.var k.value < 0 || s.cmpToUpperBound k.var k.value > 0 then pure ()
    else save := save.push front
  modify fun s => { s with diseqQueue := s.diseqQueue ++ save }
  return split_

/-! ## Integers -/

/-- `isIntegerInput`: an integer variable of the input (not a slack). -/
def isIntegerInput (s : State) (x : Nat) : Bool := s.isInteger x && !s.isAuxiliary x

/-- `nextIntegerViolation`: round robin from `nextIntegerCheckVar`, an integer
input variable whose value is not integral (and within its bounds, unless
`assumeBounds`). -/
def nextIntegerViolation (s : State) (assumeBounds : Bool) : Option Nat := Id.run do
  let n := s.numVars
  if n == 0 then return none
  let start := s.nextIntegerCheckVar
  let mut v := start
  repeat
    if isIntegerInput s v && !(s.assignment v).isIntegral && (assumeBounds || s.assignmentIsConsistent v) then
      return some v
    v := if v + 1 == n then 0 else v + 1
    if v == start then break
  return none

/-- `hasIntegerModel`: no integer violation; otherwise the round robin moves
to the first. -/
def hasIntegerModel : ArithM Bool := do
  match nextIntegerViolation (← get) true with
  | some v =>
    modify fun s => { s with nextIntegerCheckVar := v }
    return false
  | none => return true

/-- `getDioCuttingResource`: `dioSolverTurns` (10) turns of cutting, then
`rrTurns` (3) of branching. -/
def getDioCuttingResource : ArithM Bool := do
  let r := (← get).dioSolveResources
  if r > 0 then
    modify fun s => { s with dioSolveResources := if r - 1 == 0 then -3 else r - 1 }
    return true
  else
    modify fun s => { s with dioSolveResources := if r + 1 ≥ 0 then 10 else r + 1 }
    return false

def intNode (i : Int) : Node := .const (.integer i)

/-- `PreprocessRewriteEq::ppRewriteEq` of an arithmetic equality: with
`arithRewriteEq`, `(and (<= a b) (>= a b))`; otherwise its normal form
(`rewriteEqualityExt`). -/
def ppRewriteEq (rewriteEq : Bool) (eq : Node) (o : NodeOrder := {}) : Node :=
  match eq with
  | .app (.kind .EQUAL) #[a, b] =>
    if rewriteEq then Node.mkNode .AND #[Node.mkNode .LEQ #[a, b], Node.mkNode .GEQ #[a, b]]
    else ((Telos.Arith.normalizeEquality eq o).map (·.1)).getD eq
  | _ => eq

/-- `BranchAndBound::branchIntegerVariable`, with `--arith-brab`: round the
value to the nearest integer `n` first, `(or (= x n) (or (<= x (- n 1)) (>= x
(+ n 1))))`, the equality (preprocessed) getting a literal and the preferred
phase `true`. -/
def branchIntegerVariable (x : Nat) : ArithM Node := do
  let s ← get
  let r := (s.assignment x).c
  let var := (s.var x).node
  let fl := r.floor
  let ce := r.ceil
  let nearest := if ce - r > r - fl then fl else ce
  let ub := Telos.rewrite (Node.mkNode .LEQ #[var, intNode (nearest - 1)]) (← get).opts.order
  let lb := Telos.rewrite (Node.mkNode .GEQ #[var, intNode (nearest + 1)]) (← get).opts.order
  let right := Node.mkNode .OR #[ub, lb]
  let eq := Telos.rewrite (Node.mkNode .EQUAL #[var, intNode nearest]) (← get).opts.order
  let eq := match eq with
    | .app (.kind .EQUAL) _ => ppRewriteEq s.opts.rewriteEq eq s.opts.order
    | _ => eq
  -- `ensureLiteral` preprocesses (rewrites) it
  let lit := Telos.rewrite eq (← get).opts.order
  modify fun s => { s with outputs := s.outputs.push (.ensureLiteral lit) |>.push (.phase lit true) }
  return Node.mkNode .OR #[lit, right]

/-! ### The Diophantine solver -/

/-- `mkIntegerEqualityFromAssignment`: `x = β` for the integral value `β` of
`x`, as the Diophantine solver reads it (`Comparison::mkIntEquality`, then
`toSumPair`): the monomials and the constant of the sum that is `0`, with
coprime integer coefficients and its term of least absolute coefficient
positive; `none` if it has no integer solution. -/
def integerEqualityOf (s : State) (x : Nat) : Option (Array (Int × Node) × Int) := do
  let p := Poly.parse (s.var x).node
  let beta : Rat := (s.assignment x).c.floor
  let lcm := p.terms.foldl (fun (l : Nat) (c, _) => Nat.lcm l c.den) 1
  let g := p.terms.foldl (fun (g : Nat) (c, _) => Nat.gcd g c.num.natAbs) 0
  let mult : Rat := (lcm : Rat) / (g : Rat)
  let constMult := -beta * mult
  if constMult.den != 1 then none
  let terms := p.terms.map fun (c, m) => (c * mult, m)
  -- `selectAbsMinimum`: the first of least absolute coefficient
  let m := terms.foldl (fun (best : Option (Rat × Node)) t => match best with
    | none => some t
    | some b => if t.1.abs < b.1.abs then some t else best) none
  let sgn : Rat := if (m.map (·.1)).getD 1 > 0 then 1 else -1
  return (terms.map fun (c, m) => ((c * sgn).num, m), (constMult * sgn).num)

def boundsAreEqual (s : State) (x : Nat) : Bool :=
  match (s.var x).lb, (s.var x).ub with
  | some l, some u => (s.constraint l).value == (s.constraint u).value
  | _, _ => false

/-- `callDioSolver`: the equations of the integer variables whose bounds became
equal (with the explanations of the bounds), then a conflict of the solver,
if any. -/
def callDioSolver : ArithM (Option (Node × Option LinCert)) := do
  modify fun s => { s with dio := { s.dio with ages := s.age, order := s.opts.order } }
  while (← get).constantIntegersHead < (← get).constantIntegers.size do
    let s ← get
    let v := s.constantIntegers[s.constantIntegersHead]!
    modify fun s => { s with constantIntegersHead := s.constantIntegersHead + 1 }
    let lb := (s.var v).lb.get!
    let ub := (s.var v).ub.get!
    let (orig, cons) :=
      if (s.constraint lb).isEquality then (mkAndOf (explainInto s lb none #[]), #[lb])
      else if (s.constraint ub).isEquality then (mkAndOf (explainInto s ub none #[]), #[ub])
      else (.app (.kind .AND) (explainInto s lb none (explainInto s ub none #[])), #[ub, lb])
    match integerEqualityOf s v with
    | none =>
      -- `x = β` has no integer solution
      let P := Telos.Arith.Poly.add (Telos.Arith.polyOf (s.var v).node) (Telos.Arith.Poly.const (-(s.assignment v).c))
      return some (orig, dioConflictCert s #[(cons, P, 1)])
    | some (monos, k) =>
      modify fun s => { s with dio := ((Dio.pushInputConstraint monos k orig cons).run s.dio).2 }
  let (r, d) := Dio.processEquationsForConflict.run (← get).dio
  modify fun s => { s with dio := d }
  let s ← get
  return r.map fun exp => (mkAndOf exp, dioConflictCert s (d.proofInputs d.conflictIndex.get!))

/-- The node of a form of the Diophantine solver: its monomials sorted in
cvc5's order (`toSumPair`), and its constant. -/
def dioPolyNode (d : Dio) (f : LForm Int) : Node × Int :=
  let monos := (f.terms.map fun (v, c) => ((c : Rat), d.varNodes[v]!)).toList.mergeSort
    fun a b => !Telos.Arith.monoLt [b.2] [a.2] d.order
  ((Poly.mk monos.toArray).node, f.const)

/-- `dioCutting`: with the speculative equations of the integer variables at
a bound (their bounds not equal), in a scope that is then popped, the cut of a
plane `p + k = 0` of the solver: `(or (<= p (- k)) (>= p (- k)))`, rewritten
(its gcd does not divide `k`). -/
def dioCutting : ArithM (Option Node) := do
  modify fun s => { s with dio := { s.dio with ages := s.age, order := s.opts.order } }
  let s ← get
  let saved := s.dio.mark
  for v in [0:s.numVars] do
    if s.isInteger v && ((s.var v).cmpAssignmentUB == 0 || (s.var v).cmpAssignmentLB == 0) &&
        !boundsAreEqual s v then
      if let some (monos, k) := integerEqualityOf s v then
        modify fun s => { s with dio := ((Dio.pushInputConstraint monos k Node.mkTrue).run s.dio).2 }
  let (plane, d) := Dio.processEquationsForCut.run (← get).dio
  -- (the scope's pop prints its event)
  modify fun s => { s with dio := d.restore saved, outputs := s.outputs.push .scopePop }
  let some f := plane | return none
  if f.isConstant then return none
  let (p, k) := dioPolyNode d f
  let c := intNode (-k)
  return some (Telos.rewrite (Node.mkNode .OR #[Node.mkNode .LEQ #[p, c], Node.mkNode .GEQ #[p, c]]) (← get).opts.order)

/-- `roundRobinBranch`: the lemmas of the next integer violation. -/
def roundRobinBranch : ArithM (Array Node) := do
  if ← hasIntegerModel then return #[]
  return #[← branchIntegerVariable (← get).nextIntegerCheckVar]

/-- `TheoryArithPrivate::postCheck`: whether a conflict or a lemma was sent. -/
def postCheck (full : Bool) : ArithM Bool := do
  if !(← anyConflict) then
    while (← get).learnedBoundsHead < (← get).learnedBounds.size do
      let s ← get
      let c := s.learnedBounds[s.learnedBoundsHead]!
      modify fun s => { s with learnedBoundsHead := s.learnedBoundsHead + 1 }
      let _ ← assertionCases c
      if ← anyConflict then break
  if ← anyConflict then
    modify fun s => { s.commitAssignmentChanges with qflraStatus := .unsat }
    revertOutOfConflict
    outputConflicts
    return true
  let mut emitted := false
  let useSimplex := (← get).qflraStatus != .sat
  if useSimplex then emitted ← solveRealRelaxation full
  match (← get).qflraStatus with
  | .sat | .unknown => modify fun s => s.commitAssignmentChanges
  | .unsat =>
    modify fun s => s.commitAssignmentChanges
    revertOutOfConflict
    outputConflicts
    emitted := true
  -- unate propagation (`arithPropagationMode=BOTH_PROP`)
  if !emitted then
    while (← get).propListHead < (← get).propList.size && !(← anyConflict) do
      let some curr ← popPropList | continue
      match ((← get).constraint curr).type with
      | .lowerBound => unatePropLowerBound curr (← popPropList)
      | .upperBound => unatePropUpperBound curr (← popPropList)
      | .equality =>
        let pl ← popPropList
        let pu ← popPropList
        unatePropEquality curr pl pu
      | .disequality => pure ()
    if ← anyConflict then
      revertOutOfConflict
      modify fun s => { s with qflraStatus := .unsat }
      outputConflicts
      emitted := true
  modify fun s => { s with propList := #[], propListHead := 0 }
  if !emitted && full then emitted ← splitDisequalities
  -- (`hasIntegerModel` moves the round robin: only called then)
  let intViolation ← if !emitted && full then (do let h ← hasIntegerModel; pure !h) else pure false
  if intViolation then
    -- the Diophantine solver (`callDioSolver`, `dioCutting`)
    if let some (conflict, cert) ← callDioSolver then
      revertOutOfConflict
      modify fun s => { s with blackBox := s.blackBox <|> some (conflict, cert) }
      outputConflicts
      emitted := true
    if !emitted && (← get).hasDoneWorkSinceCut then
      if ← getDioCuttingResource then
        if let some lem ← dioCutting then
          modify fun s => { s with hasDoneWorkSinceCut := false }
          if ← sendLemma "ARITH_DIO_CUT" lem (orCert lem) then emitted := true
    -- branch and bound (`roundRobinBranch`), until a lemma that was not sent
    -- before
    let mut tried : Std.HashSet Key := {}
    repeat
      if emitted then break
      let mut tryNew := false
      let lems ← roundRobinBranch
      for lem in lems do
        if tried.contains ⟨lem⟩ then continue
        tried := tried.insert ⟨lem⟩
        tryNew := true
        if ← sendLemma "ARITH_BB_LEMMA" lem (orCert (Telos.rewrite lem (← get).opts.order)) then emitted := true
      if !emitted then
        let n := (← get).numVars
        modify fun s => { s with nextIntegerCheckVar := if s.nextIntegerCheckVar + 1 == n then 0 else s.nextIntegerCheckVar + 1 }
      if emitted || !tryNew then break
  return emitted

/-! ## Row bound propagation (`propagateCandidatesNew`) -/

/-- `getBestImpliedBound`: the strongest bound of type `t` on `v` implied by
`v ⋈ r` (the first upper bound at or above `r`, or the last lower bound at or
below it). -/
def getBestImpliedBound (s : State) (v : Nat) (t : CType) (r : DeltaRational) : Option Nat := Id.run do
  let m := s.scm[v]!
  let (i, _) := scmFind m r
  if t == .upperBound then
    for j in [i:m.size] do
      if let some ub := m[j]!.2.ub then return some ub
    return none
  else
    if m.isEmpty then return none
    if i < m.size && m[i]!.1 > r && i == 0 then return none
    let mut j := if i == m.size then i - 1 else if m[i]!.1 > r then i - 1 else i
    repeat
      if let some lb := m[j]!.2.lb then return some lb
      if j == 0 then break
      j := j - 1
    return none

/-- `propagateMightSucceed`. -/
def propagateMightSucceed (s : State) (v : Nat) (ub : Bool) : Bool :=
  let cmp := if ub then (s.var v).cmpAssignmentUB else (s.var v).cmpAssignmentLB
  let hasSlack := if ub then cmp < 0 else cmp > 0
  if !hasSlack then false
  else
    let a := s.assignment v
    if s.isInteger v && !a.isIntegral then true
    else match getBestImpliedBound s v (if ub then .upperBound else .lowerBound) a with
      | none => false
      | some c => let k := s.constraint c; !k.assertedToTheTheory && k.canBePropagated && !s.hasProof c

/-- `computeRowBound`: the row's sum with each variable at the bound in the
direction `rowUb`, but `skip`. -/
def computeRowBound (s : State) (r : Nat) (rowUb : Bool) (skip : Option Nat) : DeltaRational :=
  (s.tableau.rowEntries r).foldl (fun sum id =>
    let e := s.tableau.entry id
    if some e.col == skip then sum
    else
      let vUb := rowUb == (ratSgn e.coeff > 0)
      sum + (if vUb then s.getUpperBound e.col else s.getLowerBound e.col) * e.coeff) 0

/-- `propagateRow`: the bounds of the row's other variables, and the Farkas
coefficients (the implied constraint's first). -/
def propagateRow (s : State) (r : Nat) (rowUp : Bool) (c : Nat) : Array Nat × Array Rat := Id.run do
  let v := (s.constraint c).var
  let mult : Rat := if rowUp then 1 else -1
  let mut into := #[]
  let mut farkas := #[(0 : Rat)]
  for id in s.tableau.rowEntries r do
    let e := s.tableau.entry id
    let sgn := ratSgn e.coeff
    let selectUb := if rowUp then sgn > 0 else sgn < 0
    if e.col == v then farkas := farkas.set! 0 (mult * e.coeff)
    else
      farkas := farkas.push (mult * e.coeff)
      into := into.push (if selectUb then (s.var e.col).ub.get! else (s.var e.col).lb.get!)
  return (into, farkas)

/-- The negation of a literal (`Node::negate`). -/
def negateLit : Node → Node
  | .app (.kind .NOT) #[a] => a
  | n => Node.notNode n

/-- `flattenImplication` of `(=> (and a₁ … aₙ) b)`: `(or (not a₁) … (not aₙ) b)`,
without repetitions. -/
def flattenImplication (ants : Array Node) (b : Node) : Node := Id.run do
  let mut out := #[]
  for a in ants do
    let n := negateLit a
    if !out.contains n then out := out.push n
  if !out.contains b then out := out.push b
  return .app (.kind .OR) out

/-- `rowImplicationCanBeApplied`: a short row's implication is a lemma
(`ARITH_ROW_IMPL`), a long one's a propagation. -/
def rowImplicationCanBeApplied (r : Nat) (rowUp : Bool) (implied : Nat) : ArithM Bool := do
  let s ← get
  let k := s.constraint implied
  if k.assertedToTheTheory || !k.canBePropagated || s.hasProof implied then return false
  let (explain, farkas) := propagateRow s r rowUp implied
  if s.tableau.rowLength r ≤ 8 then  -- `arithPropAsLemmaLength`
    let ants := explain.foldl (fun acc c => explainInto s c none acc) #[]
    -- `externalImplication`: the antecedent is one literal, or a conjunction
    let ants := if ants.isEmpty then #[Node.mkTrue] else ants
    let b := k.literal.get!
    let clause := flattenImplication ants b
    let cert := farkasCert s none implied (negate b) explain farkas
    let _ ← sendLemma "ARITH_ROW_IMPL" clause cert
  else
    impliedByFarkas implied explain farkas
    modify fun s => s.tryToPropagate implied
  return true

/-- `tryToPropagate` of a row: the bound implied for `v`, if it is stronger. -/
def tryToPropagateRow (r : Nat) (rowUp : Bool) (v : Nat) (vUb : Bool) (bound : DeltaRational) : ArithM Bool := do
  let s ← get
  let weaker := if vUb then s.cmpToUpperBound v bound < 0 else s.cmpToLowerBound v bound > 0
  if !weaker then return false
  match getBestImpliedBound s v (if vUb then .upperBound else .lowerBound) bound with
  | some implied => rowImplicationCanBeApplied r rowUp implied
  | none => return false

/-- `rowLacksBound`: the first entry whose variable lacks the bound. -/
def rowLacksBound (s : State) (r : Nat) (rowUb : Bool) : Option Entry :=
  (s.tableau.rowEntries r).findSome? fun id =>
    let e := s.tableau.entry id
    let selectUb := rowUb == (ratSgn e.coeff > 0)
    let has := if selectUb then (s.var e.col).ub.isSome else (s.var e.col).lb.isSome
    if has then none else some e

/-- `attemptSingleton`. -/
def attemptSingleton (r : Nat) (rowUp : Bool) : ArithM Bool := do
  let s ← get
  let some e := rowLacksBound s r rowUp | return false
  let vUp := rowUp == (ratSgn e.coeff < 0)
  if propagateMightSucceed s e.col vUp then
    let bound := computeRowBound s r rowUp (some e.col) / (-e.coeff)
    tryToPropagateRow r rowUp e.col vUp bound
  else return false

/-- `attemptFull`. -/
def attemptFull (r : Nat) (rowUp : Bool) : ArithM Bool := do
  let s ← get
  let cands := (s.tableau.rowEntries r).filterMap fun id =>
    let e := s.tableau.entry id
    if propagateMightSucceed s e.col (rowUp == (ratSgn e.coeff < 0)) then some e else none
  if cands.isEmpty then return false
  let slack := computeRowBound s r rowUp none
  let mut any := false
  for e in cands do
    let s ← get
    let activeUp := rowUp == (ratSgn e.coeff > 0)
    let vUb := rowUp == (ratSgn e.coeff < 0)
    let active := if activeUp then s.getUpperBound e.col else s.getLowerBound e.col
    let implied := (slack - active * e.coeff) / (-e.coeff)
    if ← tryToPropagateRow r rowUp e.col vUb implied then any := true
  return any

/-- `propagateCandidateRow` (cvc5 skips rows of 16 entries or more at random,
which telos does not). -/
def propagateCandidateRow (r : Nat) : ArithM Unit := do
  let s ← get
  let has := (s.btracking.get r).hasBounds
  let len := s.tableau.rowLength r
  if has.lb == len then let _ ← attemptFull r false
  else if has.lb + 1 == len then let _ ← attemptSingleton r false
  if has.ub == len then let _ ← attemptFull r true
  else if has.ub + 1 == len then let _ ← attemptSingleton r true

/-- `propagateCandidatesNew`: the rows of the updated bounds' variables. -/
def propagateCandidatesNew : ArithM Unit := do
  let s ← get
  if s.updatedBounds.isEmpty then return
  -- `dumpUpdatedBoundsToRows`
  let mut rows : DenseSet := {}
  for v in s.updatedBounds.keys do
    if s.tableau.isBasic v then rows := rows.add (s.tableau.basicToRowIndex v)
    else
      for id in s.tableau.colEntries v do rows := rows.add (s.tableau.entry id).row
  modify fun s => { s with updatedBounds := s.updatedBounds.purge }
  if !rows.isEmpty then processBoundsQueueTracking
  while !rows.isEmpty do
    let r := rows.back
    rows := rows.popBack
    propagateCandidateRow r

/-- `TheoryArithPrivate::propagate`: row bound propagation after a `sat`
relaxation, then the constraint database's propagations not asserted. -/
def propagate : ArithM Unit := do
  if (← get).qflraStatus == .sat && !(← get).updatedBounds.isEmpty then propagateCandidatesNew
  else modify fun s => { s with updatedBounds := s.updatedBounds.purge }
  while (← get).toPropagateHead < (← get).toPropagate.size do
    let s ← get
    let c := s.toPropagate[s.toPropagateHead]!
    modify fun s => { s with toPropagateHead := s.toPropagateHead + 1 }
    let k := s.constraint c
    if !k.assertedToTheTheory then
      modify fun s => { s with outputs := s.outputs.push (.propagate k.literal.get!) }

/-! ## The model -/

/-- `getDeltaValue`: the delta-rational value of a term in the assignment
(constants, variables, sums, products by constants); none otherwise. -/
partial def deltaValue (s : State) (n : Node) : Option DeltaRational :=
  match constVal? n with
  | some c => some (DeltaRational.ofRat c)
  | none =>
    match s.asArithVar? n with
    | some x => some (s.assignment x)
    | none =>
      match n with
      | .app (.kind .ADD) cs => cs.foldlM (fun acc c => (deltaValue s c).map (acc + ·)) 0
      | .app (.kind .MULT) #[a, b] =>
        match constVal? a, constVal? b with
        | some c, _ => (deltaValue s b).map (· * c)
        | _, some c => (deltaValue s a).map (· * c)
        | _, _ => none
      | .app (.kind .TO_REAL) #[a] => deltaValue s a
      | _ => none

/-- An equality status of two terms (`EqualityStatus`), for theory
combination. -/
inductive EqStatus where
  | trueAndPropagated | falseAndPropagated | isTrue | isFalse | trueInModel | falseInModel | unknown
  deriving BEq, Inhabited

/-- `TheoryArithPrivate::getEqualityStatus`: by the values of the terms, once
the real relaxation is solved. -/
def equalityStatus (a b : Node) : ArithM EqStatus := do
  if a == b then return .trueInModel
  let s ← get
  if s.qflraStatus == .unknown then return .unknown
  match deltaValue s a, deltaValue s b with
  | some x, some y => return if x == y then .trueInModel else .falseInModel
  | _, _ => return .unknown

/-- `DeltaRational::seperatingDelta`: lower `res` so that `δ` keeps `a < b`. -/
def separatingDelta (res : Rat) (a b : DeltaRational) : Rat :=
  let c := a.cmp b
  if c == 0 then res else
  let (mn, mx) := if c < 0 then (a, b) else (b, a)
  if mn.c == mx.c || mn.k == mx.k then res
  else
    let den := if mx.k - mn.k < 0 then mn.k - mx.k else mx.k - mn.k
    let ratio := (mx.c - mn.c) / den
    if ratio < res then ratio else res

/-- `deltaValueForTotalOrder`: a value of `δ` that keeps the order of the
assignments, the bounds and the disequalities' values (half the least
separating value, at most 2). -/
def deltaValueForTotalOrder (s : State) : Rat := Id.run do
  let mut vals : Array DeltaRational := s.diseqQueue.map fun c => (s.constraint c).value
  for x in [0:s.numVars] do
    vals := vals.push (s.assignment x)
    if let some lb := (s.var x).lb then vals := vals.push (s.constraint lb).value
    if let some ub := (s.var x).ub then vals := vals.push (s.constraint ub).value
  let sorted := vals.qsort (fun a b => a < b)
  let mut uniq : Array DeltaRational := #[]
  for v in sorted do
    if uniq.back? != some v then uniq := uniq.push v
  let mut min : Rat := 2
  for i in [1:uniq.size] do min := separatingDelta min uniq[i-1]! uniq[i]!
  return min / 2

/-- `collectModelValues`: the values of the variables that are not slacks, with
`δ` substituted. -/
def modelValues (s : State) : Array (Node × Rat) :=
  let δ := deltaValueForTotalOrder s
  (Array.range s.numVars).filterMap fun x =>
    if s.isAuxiliary x then none else some (s.asNode x, (s.assignment x).substituteDelta δ)

end Telos.Solver.Arith
