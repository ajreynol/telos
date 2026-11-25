import Telos.Solver.Theory.QuantInst
import Telos.Solver.Theory.DtType
import Telos.Solver.Theory.Arith.Nl.Basic
import Telos.Solver.Rand

/-!
# Counterexample-guided instantiation

A port of cvc5's `InstStrategyCegqi` and `CegInstantiator`
(`src/theory/quantifiers/cegqi/`), with the instantiators of arithmetic
(`ArithInstantiator`) and datatypes (`DtInstantiator`), in the configuration of
safe mode with full-strict proofs: `cegqi-midpoint`, no infinities, so that no
virtual terms (deltas, infinities) are ever made; no nested quantifier
elimination; bit-vectors and witness terms are outside safe mode.

A formula `q` that the strategy handles (`isCbqiQuant`) is owned by it. When `q`
is preregistered, the counterexample lemma `(or (not G) (not body[e]))` is sent
(`QUANTIFIERS_CEGQI_CEX`), for its counterexample literal `G` and its
instantiation constants `e`, telos's internal constants `@ce.q` and
`@ic.q.i`. The SAT solver decides `G` true first (`ceLits`,
`DecisionStrategySingleton`); if it is false, `q` is inactive: `body` has no
counterexample in this context. At last call, an instance of each active
formula is constructed from the model and the literals over `e`
(`constructInstantiation`): each variable is solved for in an equality, or
bounded by the assertions (model-based projection), or given its value.

The counterexample lemmas are not valid, and have no certificate. No refutation
needs them: `G` occurs in no other clause but negated, so a clause they derive
has `(not G)`, which nothing resolves. An `unsat` rests on the instances
(`instantiate`).
-/

namespace Telos.Solver.Quant

open _root_.Telos.Solver.Arith.Nl (MSum mkConstOf isRealTerm castToReal)
open _root_.Telos.Solver.Arith (constVal?)

/-! ## What is handled -/

/-- `CegInstantiator::isCbqiKind`. -/
def isCbqiKind (k : Kind) : Bool :=
  k == .ADD || k == .SUB || k == .NEG || k == .GEQ || k == .LEQ || k == .GT || k == .LT || k == .EQUAL ||
    k == .MULT || k == .DIVISION || k == .DIVISION_TOTAL || k == .INTS_DIVISION || k == .INTS_DIVISION_TOTAL ||
    k == .INTS_MODULUS || k == .INTS_MODULUS_TOTAL || k == .TO_INTEGER || k == .IS_INTEGER || k == .TO_REAL ||
    k == .ABS || k == .ITE || k == .FORALL ||
    k.theoryId == .THEORY_DATATYPES || k.theoryId == .THEORY_BOOL

/-- `CegInstantiator::isCbqiTerm`. -/
def isCbqiTerm (n : Node) : Bool := Id.run do
  let mut seen : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    match cur with
    | .boundVar .. | .skolem .. => continue
    | _ => pure ()
    if !hasBoundVar cur then continue
    if cur.getKind == .FORALL then work := work.push (quantBody cur)
    else
      match cur with
      | .app _ cs =>
        if !isCbqiKind cur.getKind then return false
        work := work ++ cs
      | _ => return false
  return true

/-- `CegInstantiator::isCbqiSort`. -/
partial def isCbqiSort (T : TypeNode) (seen : List TypeNode := []) : Bool :=
  if seen.contains T then true else
  match T with
  | .integer | .real | .boolean => true
  | .datatype .. | .tuple .. | .unitTuple =>
    (List.range (DT.numConstructors T)).all fun i =>
      ((DT.fieldTypes? T i).getD []).all fun F => isCbqiSort F (T :: seen)
  | _ => false

/-- `CegInstantiator::isCbqiQuant`. -/
def isCbqiQuant (q : Node) : Bool :=
  if q.isBoundedForall then false else
  let pats := match q.getChildren[2]? with
    | some p => p.getChildren.any (·.getKind == .INST_PATTERN)
    | none => false
  !pats && (quantVars q).all (fun v => match v.typeHint with
    | some T => isCbqiSort T
    | none => false) && isCbqiTerm q

/-! ## Constants -/

/-- The counterexample literal of the formula numbered `i`. -/
def ceLit (i : Nat) : Node := .var s!"@ce.{i}" .boolean

/-- The instantiation constant of variable `j` of the formula numbered `i`. -/
def instConst (i j : Nat) (T : TypeNode) : Node := .var s!"@ic.{i}.{j}" T

/-- The formula's number of an instantiation constant. -/
def instConstOf? : Node → Option Nat
  | .var n _ => if n.startsWith "@ic." then ((n.splitOn ".")[1]?).bind String.toNat? else none
  | _ => none

/-- The numbers of the formulas whose instantiation constants occur in `n`
(not below skolems). -/
def instConstsIn (n : Node) : Array Nat := Id.run do
  let mut out := #[]
  let mut seen : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    if let some i := instConstOf? cur then
      if !out.contains i then out := out.push i
    match cur with
    | .app _ cs | .skolem _ cs => work := work ++ cs
    | _ => pure ()
  return out

/-- The free symbols of `n` (constants and skolems). -/
def symbolsOf (n : Node) : Array Node := Id.run do
  let mut out := #[]
  let mut seen : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    match cur with
    | .var .. => out := out.push cur
    | .skolem .. => out := out.push cur
    | .app op cs =>
      if let .node _ f := op then
        match f with
        | .skolem .. => pure ()
        | _ => work := work.push f
      work := work ++ cs.reverse
    | _ => pure ()
  return out

def subtermOf (t n : Node) : Bool := Id.run do
  let mut seen : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if cur == t then return true
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    match cur with
    | .app _ cs => work := work ++ cs
    | _ => pure ()
  return false

/-- `n` with each `vars[i]` replaced by `subs[i]`, simultaneously. -/
partial def substNodes (vars subs : Array Node) (n : Node) : Node :=
  let σ : Std.HashMap Key Node := (vars.zip subs).foldl (fun m (v, t) => if m.contains ⟨v⟩ then m else m.insert ⟨v⟩ t) {}
  let rec go (n : Node) : StateM (Std.HashMap Key Node) Node := do
    if let some t := σ.get? ⟨n⟩ then return t
    match n with
    | .app op cs =>
      if let some r := (← get).get? ⟨n⟩ then return r
      let mut ds := #[]
      for c in cs do ds := ds.push (← go c)
      let r := if ds == cs then n else .app op ds
      modify (·.insert ⟨n⟩ r)
      return r
    | _ => return n
  ((go n).run {}).1

/-! ## The instantiator -/

/-- `CegTermType`. -/
inductive CTT where
  | equal | lower | lowerStrict | upper | upperStrict
  deriving BEq, Inhabited

namespace CTT
def strict : CTT → CTT
  | .lower => .lowerStrict
  | .upper => .upperStrict
  | c => c
def neg : CTT → CTT
  | .lower => .upper
  | .upper => .lower
  | .lowerStrict => .upperStrict
  | .upperStrict => .lowerStrict
  | c => c
def isStrict (c : CTT) : Bool := c == .lowerStrict || c == .upperStrict
def isUpper (c : CTT) : Bool := c == .upper || c == .upperStrict
end CTT

/-- `TermProperties`: the type of the bound, and the coefficient. -/
structure TProp where
  type : CTT := .equal
  coeff : Option Rat := none
  deriving BEq, Inhabited

def TProp.basic (p : TProp) : Bool := p.coeff.isNone

/-- `SolvedForm`. -/
structure SolvedForm where
  vars : Array Node := #[]
  subs : Array Node := #[]
  props : Array TProp := #[]
  nonBasic : Array Node := #[]
  theta : Option Rat := none
  deriving Inhabited

/-- A bound of a variable: the term, the coefficient of the variable, and
whether it is strict (the delta, `1` or `-1`). -/
structure Bound where
  term : Node
  coeff : Option Rat
  delta : Rat
  deriving Inhabited

/-- The state of a call of `check`. -/
structure CegState where
  rd : Round
  /-- The effort: 1 standard, 2 standard with model values, 3 full. -/
  effort : Nat := 1
  stackVars : Array Node := #[]
  solved : Std.HashSet Key := {}
  subsProc : Std.HashMap Key (Array (Node × Option Rat)) := {}
  index : Std.HashMap Key Nat := {}
  progVars : Std.HashMap Key (Array Node × Bool) := {}
  active : Array Node := #[]
  deriving Inhabited

/-- What a call of `check` reads. -/
structure CegEnv where
  q : Node
  inst : CegInst
  ctx : Ctx
  varSet : Std.HashSet Key
  /-- The terms of the classes, by representative. -/
  eqcs : Std.HashMap Key (Array Node)
  /-- The representatives of each type. -/
  typeEqcs : Std.HashMap (Option TypeNode) (Array Node)
  /-- The literals of arithmetic, datatypes, and UF. -/
  asserts : Theory → Array Node
  value : Node → Option Node

abbrev CM := ReaderT CegEnv (StateT CegState EM)

def crw (n : Node) : CM Node := return (← read).ctx.rewrite n

/-- `computeProgVars`: the variables in `n`, and whether it is ineligible. -/
partial def progVars (n : Node) : CM (Array Node × Bool) := do
  if let some r := (← get).progVars.get? ⟨n⟩ then return r
  let e ← read
  let r ← if e.varSet.contains ⟨n⟩ then do
      -- (a selector registered as a variable has that of its argument)
      pure (#[n], false)
    else match n with
      | .skolem .. => pure (#[], !subtermOf n e.q)
      | .var .. =>
        pure (#[], (instConstOf? n).isSome && !subtermOf n e.q)
      | .app _ cs =>
        let cs := if n.getKind == .FORALL || n.getKind == .EXISTS then #[cs[1]!] else cs
        let mut vs : Array Node := #[]
        let mut inelig := false
        for c in cs do
          let (ws, i) ← progVars c
          for w in ws do if !vs.contains w then vs := vs.push w
          inelig := inelig || i
        -- selectors applied to variables are variables
        if (DT.selApp? n).isSome && vs.contains cs[0]! then vs := vs.push n
        pure (vs, inelig)
      | _ => pure (#[], false)
  modify fun s => { s with progVars := s.progVars.insert ⟨n⟩ r }
  return r

def eligible (n : Node) : CM Bool := return !(← progVars n).2
def varsOf (n : Node) : CM (Array Node) := return (← progVars n).1
def hasVar (n pv : Node) : CM Bool := return (← varsOf n).contains pv

def isIntTerm (n : Node) : Bool := n.typeHint == some .integer
def isArithType (T : Option TypeNode) : Bool := T == some .integer || T == some .real

def mulC (c : Rat) (t : Node) : Node := Node.mkNode .MULT #[mkConstOf t c, t]

/-- The monomial sum of a polynomial, which sees through `to_real` (cvc5's sums
mix integers and reals). -/
def msumOfPoly (p : _root_.Telos.Arith.Poly) : MSum :=
  (p.map fun (m, c) =>
    let t : Option Node := match m with
      | [] => none
      | [v] => some v
      | vs =>
        let real := vs.any isRealTerm
        some (Node.mkNode .MULT (vs.map fun v => if real then castToReal v else v).toArray)
    (t, some (Arith.Nl.mkConstQ c))).toArray

/-- `getMonomialSumLit`. -/
def msumLit (atom : Node) : Option MSum :=
  match atom with
  | .app (.kind .GEQ) #[a, b] | .app (.kind .EQUAL) #[a, b] =>
    if isArithType a.typeHint then
      some (msumOfPoly ((_root_.Telos.Arith.polyOf a).add ((_root_.Telos.Arith.polyOf b).scale (-1))))
    else none
  | _ => none

/-- `applySubstitution`: the result, and the coefficient it comes with. -/
def applySubst (intType : Bool) (n : Node) (vars subs : Array Node) (props : Array TProp) (nonBasic : Array Node)
    (tryCoeff : Bool := true) : CM (Option (Node × Option Rat)) := do
  let n ← crw n
  let pvs ← varsOf n
  if pvs.all (!nonBasic.contains ·) then
    let r := substNodes vars subs n
    return some (← if r == n then pure r else crw r, none)
  if !intType then
    -- with divisions
    let mut nsubs := #[]
    for (s, p) in subs.zip props do
      match p.coeff with
      | some c =>
        nsubs := nsubs.push (← crw (Node.mkNode .TO_INTEGER #[Node.mkNode .MULT #[.const (.rational (1 / c)), castToReal s]]))
      | none => nsubs := nsubs.push s
    let r := substNodes vars nsubs n
    return some (← if r == n then pure r else crw r, none)
  if !tryCoeff then return none
  let msum := msumOfPoly (_root_.Telos.Arith.polyOf n)
  -- each monomial: its coefficient, its term, and the coefficient of its variable
  let mut coeff : Option Rat := none
  let mut parts : Array (Rat × Option Node × Option Rat) := #[]
  for (k, c) in msum do
    let cv := MSum.coeffVal c
    match k with
    | none => parts := parts.push (cv, none, none)
    | some v =>
      match vars.findIdx? (· == v) with
      | some i =>
        let pc := props[i]!.coeff
        if let some d := pc then coeff := some ((coeff.getD 1) * d)
        parts := parts.push (cv, some subs[i]!, pc)
      | none => parts := parts.push (cv, some v, none)
  let some cf := coeff | return none
  let mut children := #[]
  for (c, t, pc) in parts do
    let cc := cf / (pc.getD 1) * c
    children := children.push (match t with
      | some t => mulC cc t
      | none => mkConstOf n cc)
  let r ← crw (if children.size == 1 then children[0]! else Node.mkNode .ADD children)
  if vars.any (subtermOf · r) then return none
  return some (r, some cf)

def applySf (intType : Bool) (n : Node) (sf : SolvedForm) (tryCoeff : Bool := true) : CM (Option (Node × Option Rat)) :=
  applySubst intType n sf.vars sf.subs sf.props sf.nonBasic tryCoeff

/-- `applySubstitutionToLiteral`. -/
def applyLit (lit : Node) (sf : SolvedForm) : CM (Option Node) := do
  let pvs ← varsOf lit
  if pvs.all (!sf.nonBasic.contains ·) then
    let r := substNodes sf.vars sf.subs lit
    return some (← if r == lit then pure r else crw r)
  let (atom, pol) := match lit with
    | .app (.kind .NOT) #[a] => (a, false)
    | a => (a, true)
  let some (l, r, k) := (match atom with
    | .app (.kind .GEQ) #[a, b] => some (a, b, Kind.GEQ)
    | .app (.kind .EQUAL) #[a, b] =>
      if !pol && isArithType a.typeHint then some (Node.mkNode .SUB #[a, b], mkConstOf a 0, Kind.EQUAL) else none
    | _ => none) | return none
  let l ← crw l
  if !(← eligible l) then return none
  let some (l', _) ← applySf false l sf | return none
  let a := Node.mkNode k #[l', r]
  return some (← crw (if pol then a else Node.notNode a))

/-- The result of isolating a variable: whether it is an upper (`1`) or lower
(`-1`) bound, its coefficient, and the value. `solve_arith`. -/
def solveArith (pv atom : Node) : CM (Option (CTT × Option Rat × Node)) := do
  let some msum := msumLit atom | return none
  let k := atom.getKind
  let int := isIntTerm pv
  let isRealPart (x : Option Node × Option Node) : Bool := match x.1 with
    | some t => !isIntTerm t
    | none => false
  let mixed := int && msum.any fun x => isRealPart x || (MSum.coeffVal x.2).den != 1
  let mut ires : Int := 0
  let mut c : Option Node := none
  let mut val : Node := default
  if !mixed then
    (ires, c, val) := MSum.isolate pv msum k
    if ires == 0 then return none
    val ← crw val
  else
    -- mixed: the integer and the other parts, scaled to integers
    let den : Nat := msum.foldl (fun d x => if isRealPart x then d else Nat.lcm d (MSum.coeffVal x.2).den) 1
    let scaled := msum.map fun (k, v) => (k, some (Arith.Nl.mkConstQ (MSum.coeffVal v * den)))
    let reals := scaled.filter isRealPart
    (ires, c, val) := MSum.isolate pv (scaled.filter (!isRealPart ·)) k
    if ires == 0 then return none
    if !reals.isEmpty then
      let realPart := castToReal (MSum.toNode reals)
      -- (the real part is on the side of the other terms)
      let up := ((MSum.get? scaled (some pv)).map MSum.coeffVal).getD 1 > 0
      let rp : Node := if up then Node.mkNode .MULT #[.const (.rational (-1)), realPart] else realPart
      val := Node.mkNode .TO_INTEGER #[Node.mkNode .ADD #[castToReal val, rp]]
    val ← crw val
    if !isIntTerm val then return none
  if subtermOf pv val then return none
  if !int && isIntTerm val then val := castToReal val
  let cc := c.bind constVal?
  if k == .EQUAL then return some (.equal, cc, val)
  return some (if ires == 1 then .upper else .lower, cc, val)

/-- `getModelValue`, a constant. -/
def modelValue (n : Node) : CM (Option Node) := return (← read).value n

def ratValue (n : Node) : CM (Option Rat) := return ((← modelValue n).bind constVal?)

/-- `getModelBasedProjectionValue`, with no virtual terms. -/
def mbpValue (e t : Node) (isLower : Bool) (c : Option Rat) (me mt : Rat) (theta : Option Rat) : CM Node := do
  let newTheta : Option Rat := match c, theta with
    | some c, some th => some (th * c)
    | some c, none => some c
    | none, th => th
  let ce := me * c.getD 1
  match newTheta with
  | some th =>
    if isIntTerm e then
      let rho := if isLower then ce - mt else mt - ce
      let r : Int := rho.num % th.num
      crw (Node.mkNode (if isLower then .ADD else .SUB) #[t, .const (.integer r)])
    else pure t
  | none => pure t

/-- `pickWithProb(0.5)`, of cvc5's random numbers. -/
def coin : CM Bool := do
  let en ← getThe Eng
  let (r, g) := en.em.rng.below 1000
  modifyThe Eng fun en => { en with em := { en.em with rng := g } }
  return r < 500

/-- `postProcessInstantiationForVariable`: `c*x = t` as `x = (div_total t c)`. -/
def postProcess (pv : Node) (sf : SolvedForm) : CM (Option SolvedForm) := do
  let some i := sf.vars.findIdx? (· == pv) | return none
  let some c := sf.props[i]!.coeff | return none
  let eq ← crw (Node.eqNode (mulC c pv) sf.subs[i]!)
  let some msum := msumLit eq | return none
  let (ires, veqc, val) := MSum.isolate pv msum .EQUAL
  if ires == 0 then return none
  let val ← crw val
  let s := match veqc with
    | some d => Node.mkNode .INTS_DIVISION_TOTAL #[val, d]
    | none => val
  return some { sf with subs := sf.subs.set! i s }

/-- `doAddInstantiation`. -/
def doAdd (sf : SolvedForm) : CM Bool := do
  let e ← read
  let mut terms := #[]
  for v in e.inst.inputVars do
    let some i := sf.vars.findIdx? (· == v) | return false
    terms := terms.push sf.subs[i]!
  let rd := (← get).rd
  let (ok, rd) ← (addInstantiation rd e.q terms "QUANTIFIERS_INST_CEGQI" : EM _)
  modify fun s => { s with rd }
  return ok

/-- The kinds of instantiators. -/
def isArithVar (v : Node) : Bool := isArithType v.typeHint
def isDtVar (v : Node) : Bool := (DT.dtType? v).isSome

/-- `solve_dt`. -/
partial def solveDt (v : Node) (a b : Option Node) (sa sb : Node) : Option Node :=
  let ok (r : Node) : Option Node := if subtermOf v r then none else some r
  if a == some v then ok sb
  else if b == some v then ok sa
  else match a.bind DT.consApp?, b.bind DT.consApp? with
    | some (_, i, as), some (_, j, bs) =>
      if i != j then none else
      let sas := ((DT.consApp? sa).map (·.2.2)).getD #[]
      let sbs := ((DT.consApp? sb).map (·.2.2)).getD #[]
      (List.range as.size).findSome? fun k => solveDt v (some as[k]!) (some bs[k]!) sas[k]! sbs[k]!
    | some (T, i, as), none =>
      let sas := ((DT.consApp? sa).map (·.2.2)).getD as
      (List.range as.size).findSome? fun k => solveDt v (some as[k]!) none sas[k]! (DT.mkSel T i k sb)
    | none, some (T, i, bs) =>
      let sbs := ((DT.consApp? sb).map (·.2.2)).getD bs
      (List.range bs.size).findSome? fun k => solveDt v (some bs[k]!) none sbs[k]! (DT.mkSel T i k sa)
    | none, none => none

def triedInst (pv : Node) : CM Bool := return !((← get).subsProc.getD ⟨pv⟩ #[]).isEmpty

mutual

/-- `constructInstantiation(sf, i)`. -/
partial def construct (sf : SolvedForm) (i : Nat) : CM Bool := do
  let e ← read
  let vars := e.inst.vars
  if i == vars.size then
    -- solved for all variables
    let mut sf := sf
    for pv in (← get).active do
      if isArithVar pv && sf.nonBasic.contains pv then
        let some sf' ← postProcess pv sf | return false
        sf := sf'
    return ← doAdd sf
  let st ← get
  let isSv := !st.stackVars.isEmpty
  let pv := if isSv then st.stackVars.back! else vars[i]!
  if isSv then modify fun s => { s with stackVars := s.stackVars.pop }
  -- `activateInstantiationVariable`
  modify fun s => { s with subsProc := s.subsProc.insert ⟨pv⟩ #[], index := s.index.insert ⟨pv⟩ i,
                           active := if s.active.contains pv then s.active else s.active.push pv }
  if i + 1 < vars.size || (← get).effort != 3 then
    if ← constructBy sf pv then return true
  let effort := (← get).effort
  let useMv := effort > 1 || pv.typeHint == some .boolean
  if !(← triedInst pv) && (useMv || isSv) then
    if let some mv ← modelValue pv then
      if effort < 2 then modify fun s => { s with effort := 2 }
      if ← constructInc pv mv {} sf then return true
      modify fun s => { s with effort }
  if isSv then modify fun s => { s with stackVars := s.stackVars.push pv }
  modify fun s => { s with subsProc := s.subsProc.erase ⟨pv⟩, index := s.index.erase ⟨pv⟩,
                           active := s.active.filter (· != pv) }
  return false

/-- `constructInstantiation(sf, vinst, pv)`. -/
partial def constructBy (sf : SolvedForm) (pv : Node) : CM Bool := do
  let e ← read
  let arith := isArithVar pv
  let dt := isDtVar pv
  let int := isIntTerm pv
  -- [1] terms equal to `pv`
  if dt then
    let pvr := if e.ctx.hasTerm pv then e.ctx.rep pv else pv
    if let some ts := e.eqcs.get? ⟨pvr⟩ then
      for n in ts do
        if n == pv || !(← eligible n) then continue
        let ns : Option Node ← if (← varsOf n).isEmpty then pure (some n) else do
          match ← applySf int n sf false with
          | some (ns, _) => pure (if ← hasVar ns pv then none else some ns)
          | none => pure none
        if let some ns := ns then
          if ← constructInc pv ns {} sf then return true
          if ← triedInst pv then return false
          break
      -- `processEqualTerms`: a constructor term
      if let some c := ts.find? fun n => (DT.consApp? n).isSome then
        if let some (T, i, _) := DT.consApp? c then
          let val := DT.getInstCons pv T i
          let sels := ((DT.consApp? val).map (·.2.2)).getD #[]
          modify fun s => { s with stackVars := s.stackVars ++ sels }
          if ← constructInc pv val {} sf then return true
          modify fun s => { s with stackVars := s.stackVars.extract 0 (s.stackVars.size - sels.size) }
      if ← triedInst pv then return false
  -- [2] equalities
  if arith || dt then
    for r in e.typeEqcs.getD pv.typeHint #[] do
      let mut lhs : Array (Node × Bool × Option Rat) := #[]
      for n in e.eqcs.getD ⟨r⟩ #[] do
        if !(← eligible n) then continue
        let ns? ← if (← varsOf n).isEmpty then pure (some (n, none)) else applySf int n sf
        let some (ns, coeff) := ns? | continue
        let hv ← hasVar ns pv
        for (l, lv, lc) in lhs do
          if !(hv || lv) then continue
          if arith then
            let a := if coeff != lc then (match lc with | some c => mulC c ns | none => ns) else ns
            let b := if coeff != lc then (match coeff with | some c => mulC c l | none => l) else l
            let eq ← crw (Node.eqNode a b)
            if let some (_, c, val) ← solveArith pv eq then
              if ← constructInc pv val { type := .equal, coeff := c } sf then return true
          else
            if let some val := solveDt pv (some ns) (some l) ns l then
              if ← constructInc pv val {} sf then return true
          if ← triedInst pv then return false
        lhs := lhs.push (ns, hv, coeff)
  -- [3] assertions
  if !arith || (← get).effort == 3 then return false
  let mut uppers : Array Bound := #[]
  let mut lowers : Array Bound := #[]
  let mut seen : Std.HashSet Key := {}
  for T in [Theory.THEORY_ARITH, Theory.THEORY_UF] do
    for lit in e.asserts T do
      if seen.contains ⟨lit⟩ then continue
      seen := seen.insert ⟨lit⟩
      let (atom, _) := match lit with
        | .app (.kind .NOT) #[a] => (a, false)
        | a => (a, true)
      let isA := match atom with
        | .app (.kind .GEQ) _ => true
        | .app (.kind .EQUAL) #[a, _] => isArithType a.typeHint
        | _ => false
      if !isA then continue
      let some slit ← applyLit lit sf | continue
      if !(← hasVar slit pv) then continue
      let (us, ls) ← processAssertion pv slit
      uppers := uppers ++ us
      lowers := lowers ++ ls
  processBounds sf pv #[uppers, lowers]

/-- `ArithInstantiator::processAssertion`: the upper and lower bounds of `pv`
from the literal. -/
partial def processAssertion (pv lit : Node) : CM (Array Bound × Array Bound) := do
  let (atom, pol) := match lit with
    | .app (.kind .NOT) #[a] => (a, false)
    | a => (a, true)
  let k := atom.getKind
  let some (ires, c, val) ← solveArith pv atom | return (#[], #[])
  let int := isIntTerm pv
  let mut us := #[]
  let mut ls := #[]
  for r in [0:if k == .EQUAL && pol then 2 else 1] do
    let mut t := ires
    let mut v := val
    if k == .GEQ then
      if !pol then
        t := ires.neg
        if int then v ← crw (Node.mkNode .ADD #[val, .const (.integer (if t.isUpper then 1 else -1))])
        else t := t.strict
    else if pol then t := if r == 0 then .upper else .lower
    else
      -- a disequality: the bound in the direction of the model
      let some pvv ← ratValue pv | return (us, ls)
      let some rhs ← ratValue val | return (us, ls)
      let isUpper := !(pvv * c.getD 1 ≥ rhs)
      if int then
        t := if isUpper then .lower else .upper
        v ← crw (Node.mkNode .ADD #[val, .const (.integer (if t.isUpper then 1 else -1))])
      else t := if isUpper then .lowerStrict else .upperStrict
    let b : Bound := { term := v, coeff := c, delta := if t.isStrict then (if t.isUpper then 1 else -1) else 0 }
    if t.isUpper then us := us.push b else ls := ls.push b
  return (us, ls)

/-- `ArithInstantiator::processAssertions`, for the bounds `bs[0]` (upper
types, cvc5's index 0: `pv >= t`) and `bs[1]`. -/
partial def processBounds (sf : SolvedForm) (pv : Node) (bs : Array (Array Bound)) : CM Bool := do
  let int := isIntTerm pv
  let upperFirst ← coin
  let some pvv ← ratValue pv | return false
  let mut vals : Array (Array (Option Rat)) := #[#[], #[]]
  for rr in [0, 1] do
    vals := vals.set! rr (← bs[rr]!.mapM fun b => ratValue b.term)
  let mut bestUsed : Array (Option Nat) := #[none, none]
  for r in [0, 1] do
    let rr := if upperFirst then 1 - r else r
    if bs[rr]!.isEmpty then continue
    -- the best bound: the tightest in the model
    let mut best : Option (Nat × Rat × Rat) := none
    for j in [0:bs[rr]!.size] do
      let b := bs[rr]![j]!
      let some v := vals[rr]![j]! | continue
      let c := b.coeff.getD 1
      let (v, d) := (v / c, b.delta / c)
      let better := match best with
        | none => true
        | some (_, bv, bd) =>
          if v != bv then (if rr == 0 then v > bv else v < bv)
          else if d != bd then (if rr == 0 then d > bd else d < bd)
          else true
      if better then best := some (j, v, d)
    let some (j, _, _) := best | continue
    bestUsed := bestUsed.set! rr (some j)
    let b := bs[rr]![j]!
    -- (with midpoints, a strict bound of a real gives no instance of its own)
    if int || b.delta == 0 then
      let val ← mbpValue pv b.term (rr == 0) b.coeff pvv (vals[rr]![j]!.getD 0) sf.theta
      return ← constructInc pv val { type := if rr == 0 then .upper else .lower, coeff := b.coeff } sf
  if bs[0]!.isEmpty && bs[1]!.isEmpty then
    let val ← mbpValue pv (mkConstOf pv 0) true none pvv 0 sf.theta
    return ← constructInc pv val {} sf
  if !int then
    -- the midpoint of the bounds
    let v (rr : Nat) : CM (Option Node) := do
      match bestUsed[rr]! with
      | some j => return some (← mbpValue pv bs[rr]![j]!.term (rr == 0) none pvv (vals[rr]![j]!.getD 0) sf.theta)
      | none => return none
    let val : Option Node ← match ← v 0, ← v 1 with
      | some a, some b =>
        if a == b then pure (some a)
        else some <$> crw (Node.mkNode .MULT #[.const (.rational (1 / 2)), Node.mkNode .ADD #[a, b]])
      | some a, none => some <$> crw (Node.mkNode .ADD #[a, mkConstOf pv 1])
      | none, some b => some <$> crw (Node.mkNode .SUB #[b, mkConstOf pv 1])
      | none, none => pure none
    if let some val := val then return ← constructInc pv val {} sf
  -- the bounds that are not the best
  for r in [0, 1] do
    let rr := if upperFirst then 1 - r else r
    for j in [0:bs[rr]!.size] do
      let b := bs[rr]![j]!
      if bestUsed[rr]! == some j || b.delta != 0 then continue
      let val ← mbpValue pv b.term (rr == 0) b.coeff pvv (vals[rr]![j]!.getD 0) sf.theta
      return ← constructInc pv val { type := if rr == 0 then .upper else .lower, coeff := b.coeff } sf
  return false

/-- `constructInstantiationInc`: `prop.coeff * pv` is `n`; the solved form so
far substituted, and the next variable. -/
partial def constructInc (pv n : Node) (prop : TProp) (sf : SolvedForm) : CM Bool := do
  if n.typeHint != pv.typeHint then return false
  let done := (← get).subsProc.getD ⟨pv⟩ #[]
  if done.contains (n, prop.coeff) then return false
  modify fun s => { s with subsProc := s.subsProc.insert ⟨pv⟩ (done.push (n, prop.coeff)) }
  let nonBasic := if prop.basic then #[] else #[pv]
  let mut nsf := sf
  for j in [0:sf.subs.size] do
    if !(← hasVar sf.subs[j]! pv) then continue
    let some (t, c) ← applySubst (isIntTerm sf.vars[j]!) sf.subs[j]! #[pv] #[n] #[prop] nonBasic true | return false
    nsf := { nsf with subs := nsf.subs.set! j t }
    if let some c := c then
      let p := nsf.props[j]!
      if p.basic then nsf := { nsf with nonBasic := nsf.nonBasic.push nsf.vars[j]! }
      nsf := { nsf with props := nsf.props.set! j { p with coeff := some (c * p.coeff.getD 1) } }
  nsf := { nsf with vars := nsf.vars.push pv, subs := nsf.subs.push n, props := nsf.props.push prop }
  if let some c := prop.coeff then
    nsf := { nsf with nonBasic := nsf.nonBasic.push pv, theta := some (nsf.theta.getD 1 * c) }
  let st ← get
  let i := st.index.getD ⟨pv⟩ 0
  construct nsf (if st.stackVars.isEmpty then i + 1 else i)

end

/-! ## The strategy -/

/-- The strategy's data of the formula `q`: its number (made if needed). -/
def cegId (q : Node) : EM Nat := do
  let en ← get
  match en.cegIds.get? ⟨q⟩ with
  | some i => return i
  | none =>
    let i := en.cegQuants.size
    set { en with cegIds := en.cegIds.insert ⟨q⟩ i, cegQuants := en.cegQuants.push q }
    return i

/-- `doCbqi`. -/
def doCbqi (q : Node) : EM Bool := do
  let c ← ectx
  if !c.cegqi then return false
  match (← get).doCbqi.get? ⟨q⟩ with
  | some b => return b
  | none =>
    let b := isCbqiQuant q
    modify fun en => { en with doCbqi := en.doCbqi.insert ⟨q⟩ b }
    return b

/-- `collectCeAtoms`. -/
def collectCeAtoms (n : Node) : Std.HashSet Key × Bool := Id.run do
  let mut atoms : Std.HashSet Key := {}
  let mut nested := false
  let mut seen : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    if cur.getKind == .FORALL then nested := true
    if isBoolConnectiveTerm cur then work := work ++ cur.getChildren
    else
      atoms := atoms.insert ⟨cur⟩
      -- (either orientation: the SAT solver's atom may be the other)
      if let .app (.kind .EQUAL) #[a, b] := cur then atoms := atoms.insert ⟨Node.eqNode b a⟩
  return (atoms, nested)

/-- The quantified formulas in `n`, not those below others. -/
def topQuants (n : Node) : Array Node := Id.run do
  let mut out := #[]
  let mut seen : Std.HashSet Key := {}
  let mut work := #[n]
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains ⟨cur⟩ then continue
    seen := seen.insert ⟨cur⟩
    if cur.getKind == .FORALL then out := out.push cur
    else match cur with
      | .app _ cs => work := work ++ cs
      | _ => pure ()
  return out

/-- `registerCbqiLemma`. -/
partial def registerCbqiLemma (q : Node) : EM Unit := do
  if (← get).cegInsts.contains ⟨q⟩ then return
  let c ← ectx
  let id ← cegId q
  let g := ceLit id
  let vs := quantVars q
  let ics := vs.mapIdx fun j v => instConst id j (v.typeHint.getD .boolean)
  modify fun en => { en with cegInsts := en.cegInsts.insert ⟨q⟩ { id, inputVars := ics },
                             st := { en.st with anyInstConst := true } }
  let body := substitute vs ics (quantBody q)
  let lem := c.rewrite (Node.orNode (Node.notNode g) (Node.notNode body))
  let _ ← emitLemma { id := "QUANTIFIERS_CEGQI_CEX", lem }
  -- `registerCounterexampleLemma`: the variables, with those of the lemma's
  -- preprocessing, the reals before the integers
  let pp := c.preprocess lem
  let qSyms := symbolsOf q
  let mut vars := ics
  for s in symbolsOf (Node.mkNode .AND pp) do
    if qSyms.contains s || vars.contains s || s == g then continue
    match s.typeHint with
    | some .boolean | some (.function ..) | none => continue
    | _ => vars := vars.push s
  let ints := vars.filter isIntTerm
  let ordered := vars.filter (!isIntTerm ·) ++ ints
  let (atoms, nested) := (pp ++ pp.map c.rewrite).foldl (fun (as, b) f =>
    let (as', b') := collectCeAtoms f
    (as'.fold (fun s k => s.insert k) as, b || b')) ({}, false)
  let inst : CegInst := { id, inputVars := ics, vars := ordered, ceAtoms := atoms, nested }
  -- dependencies
  let known := (← get).cegQuants
  let parents := (instConstsIn q).filterMap fun i => known[i]?
  modify fun en => { en with
    cegInsts := en.cegInsts.insert ⟨q⟩ inst
    cegChildren := parents.foldl (fun m p => m.insert ⟨p⟩ ((m.getD ⟨p⟩ #[]).push q)) en.cegChildren }
  if !parents.isEmpty then
    let mut deps := #[]
    for p in parents do deps := (deps.push p).push (ceLit (← cegId p))
    let lem := Node.mkNode .IMPLIES #[g, Node.mkNode .AND deps]
    let _ ← emitLemma { id := "QUANTIFIERS_CEGQI_CEX_DEP", lem := c.rewrite lem }
  for q' in topQuants lem do
    if ← doCbqi q' then registerCbqiLemma q'
  modify fun en => { en with ceLits := en.ceLits.push g, ceBools := en.ceBools ++
    (#[g] ++ ics.filter (·.typeHint == some .boolean)) }

/-- `preRegisterQuantifier`. -/
def cegqiPreRegister (q : Node) : EM Unit := do
  if ← doCbqi q then registerCbqiLemma q

/-- `reset_round`: the active formulas; those whose counterexample literal is
false are inactive, and only the innermost are considered. -/
def cegqiReset : EM Unit := do
  let c ← ectx
  if !c.cegqi then return
  let mut inactive : Std.HashSet Key := {}
  let mut active : Array Node := #[]
  for q in (← get).st.asserted do
    if !(← doCbqi q) then continue
    let g := ceLit (← cegId q)
    if (← get).ceVals.get? ⟨g⟩ == some false then inactive := inactive.insert ⟨q⟩
    else if !active.contains q then active := active.push q
  let ch := (← get).cegChildren
  let inner := active.filter fun q => !(ch.getD ⟨q⟩ #[]).any active.contains
  let inner := inner.qsort c.lt
  modify fun en => { en with inactiveQuants := inactive, cegActive := inner, cegIncomplete := false }

/-- The value of `n` in the model, a constant: of the terms the model knows,
the defaults of the others, and the SAT solver's of the Boolean constants. -/
def cegValue (c : Ctx) (ceVals : Std.HashMap Key Bool) (n : Node) : Option Node := Id.run do
  if n.isConst then return some n
  let leafVal (t : Node) : Option Node :=
    match t with
    | .var _ .boolean => some (Node.mkBool ((ceVals.get? ⟨t⟩).getD false))
    | _ => match c.modelConst t with
      | some v => some v
      | none => match t.typeHint with
        | some .integer => some (.const (.integer 0))
        | some .real => some (.const (.rational 0))
        | some .boolean => some Node.mkFalse
        | _ => none
  match n with
  | .var .. | .skolem .. => return leafVal n
  | _ =>
    if let some v := c.modelConst n then return some v
    -- the leaves replaced by their values
    let rec go (n : Node) : Node :=
      if n.isConst then n else
      match n with
      | .var .. | .skolem .. => (leafVal n).getD n
      | .app (.node .APPLY_UF _) _ => (leafVal n).getD n
      | .app op cs => match c.modelConst n with
        | some v => v
        | none => .app op (cs.map go)
      | n => n
    let r := c.rewrite (go n)
    return if r.isConst then some r else none

/-- `CegInstantiator::check`, for `q`: whether an instance was added. -/
def cegCheck (rd : Round) (q : Node) : EM (Bool × Round) := do
  let c ← ectx
  let en ← get
  let some inst := en.cegInsts.get? ⟨q⟩ | return (false, rd)
  let varSet : Std.HashSet Key := inst.vars.foldl (·.insert ⟨·⟩) {}
  -- `processAssertions`
  let hasTid (T : Option TypeNode) : Bool :=
    inst.vars.any fun v =>
      (isArithVar v && isArithType T) || (isDtVar v && (match T with
        | some (.datatype ..) | some (.tuple ..) | some .unitTuple => true
        | t => isArithType t))
  let mut eqcs : Std.HashMap Key (Array Node) := {}
  let mut typeEqcs : Std.HashMap (Option TypeNode) (Array Node) := {}
  for v in inst.vars do
    if c.hasTerm v then
      let r := c.rep v
      if !eqcs.contains ⟨r⟩ then eqcs := eqcs.insert ⟨r⟩ (c.members r)
  for r in c.reps do
    if hasTid r.typeHint then
      typeEqcs := typeEqcs.insert r.typeHint ((typeEqcs.getD r.typeHint #[]).push r)
      if !eqcs.contains ⟨r⟩ then eqcs := eqcs.insert ⟨r⟩ (c.members r)
  let atomOf (l : Node) : Node := match l with
    | .app (.kind .NOT) #[a] => a
    | a => a
  let asserts (T : Theory) : Array Node :=
    (c.factsOf T).filter fun l => inst.nested || inst.ceAtoms.contains ⟨atomOf l⟩
  let value := cegValue c en.ceVals
  let env : CegEnv := { q, inst, ctx := c, varSet, eqcs, typeEqcs, asserts, value }
  let body : CM Bool := do
    -- the eligible literals with a variable
    let keep (ls : Array Node) : CM (Array Node) := ls.filterM fun l => do
      let (vs, inelig) ← progVars l
      return !inelig && !vs.isEmpty
    let ar ← keep (asserts .THEORY_ARITH)
    let uf ← keep (asserts .THEORY_UF)
    withReader (fun e => { e with asserts := fun T => if T == .THEORY_ARITH then ar else if T == .THEORY_UF then uf else #[] }) do
      for effort in [1, 3] do
        modify fun s => { s with effort, stackVars := #[], solved := {}, subsProc := {}, index := {}, active := #[] }
        if ← construct {} 0 then return true
      return false
  let (ok, s) ← (body.run env).run { rd }
  return (ok, s.rd)

/-- `InstStrategyCegqi::check`. -/
def cegqiCheck (rd : Round) : EM Round := do
  let mut rd := rd
  for q in (← get).cegActive do
    let (ok, rd') ← cegCheck rd q
    rd := rd'
    if !ok then modify fun en => { en with cegIncomplete := true }
    if rd.inConflict then break
  return rd

end Telos.Solver.Quant
