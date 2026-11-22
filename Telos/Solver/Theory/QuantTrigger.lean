import Telos.Solver.Theory.QuantState
import Telos.Solver.Rand

/-!
# Triggers of E-matching

The selection of trigger terms and the data of triggers, ported from cvc5's
`src/theory/quantifiers/ematching/` (`pattern_term_selector.cpp`,
`trigger_term_info.cpp`, `trigger_database.cpp`, `trigger.cpp`, and the
construction of the match generators of `inst_match_generator*.cpp`), in the
configuration of safe mode (`docs/theory-engine-plan.md`, Stage 10, step 2):
`trigger-sel=min`, `literal-match=use`, no relational, purified or partial
triggers, linear multi-triggers.

cvc5 matches the body of a formula with its bound variables replaced by
instantiation constants. Here the bound variables play their part: a term
"has instantiation constants" when it has a variable of the formula (outside
nested binders, where selection does not look). The instantiation constants'
terms are new nodes in cvc5, numbered in the order the substitution makes them
(post-order); trigger terms are ordered by those numbers (cvc5's
`std::map<Node, TriggerTermInfo>`), so selection numbers them the same way
(`Sel.ord`), and the nodes it makes after them.
-/

namespace Telos.Solver.Quant

/-- `TriggerTermInfo`: the variables of the formula in the term (a set), the
polarity it is required to have (`1`, `-1`, `0` for none) and the term it is
required to equal, and its weight. -/
structure TInfo where
  fv : Array Nat := #[]
  reqPol : Int := 0
  reqPolEq : Option Node := none
  weight : Int := 0
  deriving Inhabited

/-- The trigger selection modes ported (`trigger-sel`): `min`, and `all` for
the first pass of the filtering of instances. -/
inductive SelMode where
  | min | all
  deriving BEq, Inhabited

/-- The state of trigger selection for a formula: its variables, the
creation order of the nodes with its variables, and the memo of which nodes
have them; per pass, the terms visited and the trigger terms found. -/
structure Sel where
  vars : Std.HashMap Key Nat := {}
  ord : Std.HashMap Key Nat := {}
  nextOrd : Nat := 0
  hasV : Std.HashMap Key Bool := {}
  visited : Std.HashMap Key (Array Node) := {}
  tinfo : Std.HashMap Key TInfo := {}
  tkeys : Array Node := #[]
  /-- The terms excluded from triggers (`:no-pattern`, `d_user_no_gen`). -/
  excluded : Array Node := #[]
  deriving Inhabited

abbrev SelM := StateM Sel

/-- `TermUtil::hasInstConstAttr`: the node has a variable of the formula. -/
partial def hasIC (n : Node) : SelM Bool := do
  if let some b := (← get).hasV.get? ⟨n⟩ then return b
  let b ← match n with
    | .boundVar .. => pure ((← get).vars.contains ⟨n⟩)
    | .app _ cs =>
      if n.getKind == .FORALL || n.getKind == .EXISTS then pure false else
      cs.anyM hasIC
    | .skolem _ cs => cs.anyM hasIC
    | _ => pure false
  modify fun s => { s with hasV := s.hasV.insert ⟨n⟩ b }
  return b

/-- Number a node made by selection (after those of the body), once. -/
def mkd (n : Node) : SelM Node := do
  modify fun s => if s.ord.contains ⟨n⟩ then s else
    { s with ord := s.ord.insert ⟨n⟩ s.nextOrd, nextOrd := s.nextOrd + 1 }
  return n

/-- cvc5's node order on the nodes of selection: by creation; the nodes
without the formula's variables (older) first, by `lt`. -/
def selLt (lt : Node → Node → Bool) (s : Sel) (a b : Node) : Bool :=
  match s.ord.get? ⟨a⟩, s.ord.get? ⟨b⟩ with
  | some i, some j => i < j
  | none, some _ => true
  | some _, none => false
  | none, none => lt a b

/-- Number the nodes of the body with the formula's variables, as cvc5's
substitution by instantiation constants makes them: in post-order. -/
partial def numberBody (n : Node) : SelM Unit := do
  if (← get).ord.contains ⟨n⟩ then return
  if !(← hasIC n) then return
  match n with
  | .app _ cs => for c in cs do numberBody c
  | .skolem _ cs => for c in cs do numberBody c
  | _ => pure ()
  modify fun s => if s.ord.contains ⟨n⟩ then s else
    { s with ord := s.ord.insert ⟨n⟩ s.nextOrd, nextOrd := s.nextOrd + 1 }

def isVarOf (n : Node) : SelM Bool := return match n with
  | .boundVar .. => true
  | _ => false

def varNum (n : Node) : SelM (Option Nat) := return (← get).vars.get? ⟨n⟩

/-- The variables of the formula in `n` (`computeInstConstContainsForQuant`),
by number. -/
partial def fvOf (n : Node) : SelM (Array Nat) := do
  let rec go (n : Node) (acc : Array Nat) : SelM (Array Nat) := do
    if !(← hasIC n) then return acc
    match n with
    | .boundVar .. =>
      match (← get).vars.get? ⟨n⟩ with
      | some i => return if acc.contains i then acc else acc.push i
      | none => return acc
    | .app _ cs => cs.foldlM (fun a c => go c a) acc
    | .skolem _ cs => cs.foldlM (fun a c => go c a) acc
    | _ => return acc
  go n #[]

def isRelationalTrigger (n : Node) : Bool := n.getKind == .EQUAL || n.getKind == .GEQ

/-- `isUsableRelationTrigger`: `(= x t)` or `(>= x t)` for an arithmetic
variable `x` and a term `t` without variables (with its literal and
polarity). -/
def usableRelationTrigger (n : Node) : SelM (Option (Node × Bool × Bool)) := do
  let mut pol := n.getKind != .NOT
  let mut lit := if pol then n else n.getChildren[0]!
  let mut hasPol := false
  if lit.getKind == .EQUAL then
    if let .const (.boolean b) := lit.getChildren[1]! then
      hasPol := true
      pol := if b then pol else !pol
      lit := lit.getChildren[0]!
  let arith := fun (t : Node) => t.typeHint == some .integer || t.typeHint == some .real
  if (lit.getKind == .EQUAL && arith lit.getChildren[0]!) || lit.getKind == .GEQ then
    let cs := lit.getChildren
    for i in [0, 1] do
      if (← isVarOf cs[i]!) && (← varNum cs[i]!).isSome && !(← hasIC cs[1 - i]!) then
        return some (lit, hasPol, pol)
  return none

/-- `getTriggerWeight`. -/
def triggerWeight (n : Node) : SelM Int := do
  if n.getKind == .APPLY_UF then return 0
  if isAtomicTriggerKind n.getKind || (← usableRelationTrigger n).isSome then return 1
  return 2

/-- `isUsable`: every subterm with variables is an atomic trigger or a
variable. -/
partial def isUsable (n : Node) : SelM Bool := do
  if !(← hasIC n) then return true
  if isAtomicTriggerKind n.getKind then return ← n.getChildren.allM isUsable
  if ← isVarOf n then return true
  return false

def isUsableAtomicTrigger (n : Node) : SelM Bool := do
  return (← hasIC n) && isAtomicTriggerKind n.getKind && (← isUsable n)

/-- `isUsableEqTerms` (no relational triggers). -/
def isUsableEqTerms (n1 n2 : Node) : SelM Bool := do
  if ← isVarOf n1 then return false
  if ← isUsableAtomicTrigger n1 then return !(← hasIC n2)
  return false

/-- `getIsUsableEq` (no relational triggers). -/
def getIsUsableEq (n : Node) : SelM (Option Node) := do
  if n.getKind != .EQUAL then return none
  let cs := n.getChildren
  for i in [0, 1] do
    if ← isUsableEqTerms cs[i]! cs[1 - i]! then
      if i == 1 && !(← hasIC cs[0]!) then return some (← mkd (Node.eqNode cs[1]! cs[0]!))
      return some n
  return none

/-- `Node::negate`. -/
def negate (n : Node) : Node := if n.getKind == .NOT then n.getChildren[0]! else Node.notNode n

/-- `getIsUsableTrigger`. (The solving of arithmetic literals for a usable
monomial is not ported yet.) -/
def getIsUsableTrigger (n : Node) : SelM (Option Node) := do
  let mut pol := true
  let mut n := n
  if n.getKind == .NOT then
    pol := false
    n := n.getChildren[0]!
  let negTrue (n : Node) : SelM Node := do
    let e ← mkd (Node.eqNode n Node.mkTrue)
    mkd (Node.notNode e)
  if ← isVarOf n then
    if (← varNum n).isSome then
      if pol then return some n else return some (← negTrue n)
  if isRelationalTrigger n then
    match ← getIsUsableEq n with
    | some r => if pol then return some r else return some (← mkd (negate r))
    | none => return none
  if ← isUsableAtomicTrigger n then
    if pol then return some n else return some (← negTrue n)
  return none

/-- `QuantPhaseReq::getPolarity`. -/
def childPolarity (n : Node) (i : Nat) (hasPol pol : Bool) : Bool × Bool :=
  match n.getKind with
  | .AND | .OR => (hasPol, pol)
  | .IMPLIES => (hasPol, if i == 0 then !pol else pol)
  | .NOT => (hasPol, !pol)
  | .ITE => (i != 0 && hasPol, pol)
  | .FORALL => (i == 1 && hasPol, pol)
  | _ => (false, false)

/-- `QuantPhaseReq::getEntailPolarity`. -/
def childEntailPolarity (n : Node) (i : Nat) (hasPol pol : Bool) : Bool × Bool :=
  match n.getKind with
  | .AND | .OR => (hasPol && pol != (n.getKind == .OR), pol)
  | .IMPLIES => (hasPol && !pol, if i == 0 then !pol else pol)
  | .NOT => (hasPol, !pol)
  | _ => (false, false)

/-- `TriggerTermInfo::init` on the term `n`. -/
def tinfoInit (n : Node) (reqPol : Int) (reqPolEq : Option Node) : SelM Unit := do
  let ti := ((← get).tinfo.get? ⟨n⟩).getD {}
  let fv ← if ti.fv.isEmpty then fvOf n else pure ti.fv
  let ti := if ti.reqPol == 0 then { ti with reqPol, reqPolEq } else ti
  let w ← triggerWeight n
  modify fun s =>
    let keys := if s.tinfo.contains ⟨n⟩ then s.tkeys else s.tkeys.push n
    { s with tinfo := s.tinfo.insert ⟨n⟩ { ti with fv, weight := w }, tkeys := keys }

def tinfoErase (n : Node) : SelM Unit :=
  modify fun s => { s with tinfo := s.tinfo.erase ⟨n⟩, tkeys := s.tkeys.filter (· != n) }

def pushNew (a : Array Node) (t : Node) : Array Node := if a.contains t then a else a.push t

/-- `collectTermsInternal`: the trigger terms of `n`, added to `added`. -/
partial def collectTerms (nvars : Nat) (n : Node) (tstrt : SelMode) (added : Array Node)
    (pol hasPol epol hasEPol : Bool) (knowIsUsable : Bool := false) : SelM (Array Node) := do
  if let some vs := (← get).visited.get? ⟨n⟩ then
    return vs.foldl pushNew added
  modify fun s => { s with visited := s.visited.insert ⟨n⟩ #[] }
  let nk := n.getKind
  if nk == .FORALL || nk == .EXISTS then return added
  if ← isVarOf n then return added
  let mut nu : Option Node := none
  if knowIsUsable then nu := some n
  else if nk != .NOT && !(← get).excluded.contains n then
    nu ← getIsUsableTrigger n
    if let some nu' := nu then
      if nu' != n then
        let added ← collectTerms nvars nu' tstrt added pol hasPol epol hasEPol true
        modify fun s => { s with visited := s.visited.modify ⟨n⟩ (· ++ added) }
        return added
  let mut nuSingle := false
  if let some nu0 := nu then
    let mut nu1 := nu0
    let mut reqEq : Option Node := none
    if nu1.getKind == .EQUAL then
      let cs := nu1.getChildren
      if isAtomicTriggerKind cs[0]!.getKind && !(← hasIC cs[1]!) then
        if hasPol then reqEq := some cs[1]!
        nu1 := cs[0]!
    tinfoInit nu1 (if hasEPol then (if epol then 1 else -1) else 0) reqEq
    nuSingle := (((← get).tinfo.get? ⟨nu1⟩).getD {}).fv.size == nvars
    nu := some nu1
  let nrec := nu.getD n
  let mut added2 : Array Node := #[]
  let cs := nrec.getChildren
  for i in [0:cs.size] do
    let (nhp, np) := childPolarity nrec i hasPol pol
    let (nhe, ne) := childEntailPolarity nrec i hasEPol epol
    added2 ← collectTerms nvars cs[i]! tstrt added2 np nhp ne nhe
  let some nuT := nu | return added
  let _ := nuSingle
  let mut rmNu := false
  let mut added := added
  for a in added2 do
    let s ← get
    if let some ta := s.tinfo.get? ⟨a⟩ then
      let tn := (s.tinfo.get? ⟨nuT⟩).getD {}
      if tn.fv.size == ta.fv.size && tn.weight >= ta.weight then rmNu := true
      added := pushNew added a
  if rmNu && tstrt == .min then tinfoErase nuT
  else added := pushNew added nuT
  let added' := added
  modify fun s => { s with visited := s.visited.modify ⟨n⟩ (· ++ added') }
  return added

/-- `isInstanceOf`: `1` if `n1` is an instance of `n2`, `-1` if `n2` is one of
`n1`, else `0`. -/
def isInstanceOf (n1 n2 : Node) (fv1 fv2 : Array Nat) : SelM Int := do
  let mut status : Int := 0
  let mut subsVars : Array Node := #[]
  let mut visited : Array (Node × Node) := #[]
  let mut visit : Array (Node × Node) := #[(n1, n2)]
  while !visit.isEmpty do
    let cur := visit.back!
    visit := visit.pop
    if visited.contains cur then continue
    visited := visited.push cur
    let (c1, c2) := cur
    match c1, c2 with
    | .app o1 cs1, .app o2 cs2 =>
      if o1 == o2 && cs1.size == cs2.size then
        visit := visit.push cur
        for i in [0:cs1.size] do
          if cs1[i]! != cs2[i]! then visit := visit.push (cs1[i]!, cs2[i]!)
          else if (← varNum cs1[i]!).isSome then
            if subsVars.contains cs1[i]! then return 0
            subsVars := subsVars.push cs1[i]!
        continue
    | _, _ => pure ()
    let mut success := false
    for r in [0, 1] do
      if status == 0 || ((status == 1) == (r == 0)) then
        let curi := if r == 0 then c1 else c2
        if let some vi ← varNum curi then
          if !subsVars.contains curi then
            let curj := if r == 0 then c2 else c1
            if (← triggerWeight curj) == 0 then
              let fvs := if r == 0 then fv2 else fv1
              if fvs.contains vi then
                status := if r == 0 then 1 else -1
                subsVars := subsVars.push curi
                success := true
                break
    if !success then return 0
  return status

/-- `filterInstances`. -/
def filterInstances (nodes : Array Node) : SelM (Array Node) := do
  let mut fvs : Array (Array Nat) := #[]
  for n in nodes do fvs := fvs.push (← fvOf n)
  let mut active := Array.replicate nodes.size true
  for i in [0:nodes.size] do
    if !active[i]! then continue
    for j in [i + 1:nodes.size] do
      if !active[j]! then continue
      let r ← isInstanceOf nodes[i]! nodes[j]! fvs[i]! fvs[j]!
      if r == 1 then
        active := active.set! i false
        break
      else if r == -1 then active := active.set! j false
  return (nodes.zip active).filterMap fun (n, a) => if a then some n else none

/-- The trigger terms found, in cvc5's node order. -/
def sortedKeys (lt : Node → Node → Bool) : SelM (Array Node) := do
  let s ← get
  return s.tkeys.qsort (selLt lt s)

/-- `PatternTermSelector::collect` with `trigger-sel=min` and the filtering
of instances: the trigger terms of the body and their information. -/
def collectPatTerms (lt : Node → Node → Bool) (nvars : Nat) (body : Node) :
    SelM (Array (Node × TInfo)) := do
  -- the first pass, all trigger terms, then those that are not instances
  modify fun s => { s with visited := {}, tinfo := {}, tkeys := #[] }
  let _ ← collectTerms nvars body .all #[] true true false true
  let pats2 ← sortedKeys lt
  let temp ← filterInstances pats2
  modify fun s => { s with visited := {}, tinfo := {}, tkeys := #[] }
  for t in pats2 do
    if !temp.contains t then modify fun s => { s with visited := s.visited.insert ⟨t⟩ #[] }
  let _ ← collectTerms nvars body .min #[] true true false true
  let ks ← sortedKeys lt
  let s ← get
  return ks.map fun k => (k, (s.tinfo.get? ⟨k⟩).getD {})

/-- `isSimpleTrigger`. -/
def isSimpleTrigger (n : Node) : SelM Bool := do
  let mut t := if n.getKind == .NOT then n.getChildren[0]! else n
  if t.getKind == .EQUAL then
    if !(← hasIC t.getChildren[1]!) then t := t.getChildren[0]!
  if !isAtomicTriggerKind t.getKind then return false
  for c in t.getChildren do
    if !(← isVarOf c) && (← hasIC c) then return false
  return true

/-! ## Match generators -/

/-- A candidate generator (`candidate_generator.cpp`): of the terms of an
operator (`QE`), with the classes excluded; of the disequalities (`litDeq`:
the equalities in the class of `false`, of the type of `typ`); of the classes
of a type (`all`). -/
inductive CGKind where
  | qe (op : Node) (exclude : Array Node)
  | litDeq (k : Kind) (typ : Option TypeNode)
  | all (typ : Option TypeNode)
  deriving Inhabited

/-- The mode of a candidate generator of the terms of an operator. -/
inductive CGMode where
  | none | db | eqc | ident
  deriving BEq, Inhabited

/-- The state of a candidate generator in a round. -/
structure CGState where
  mode : CGMode := .none
  list : Array Node := #[]
  idx : Nat := 0
  eqc : Option Node := none
  firstTime : Bool := false
  deriving Inhabited

/-- An `InstMatchGenerator` (`kind := .std`), or the head of a linear
multi-trigger (`.multi`). `childTypes`: for each child of the match pattern,
the variable it binds (`≥ 0`), `-1` for a term to be equal, `-2` for a
generator. -/
inductive GKind where
  | std | multi
  deriving BEq, Inhabited

structure Gen where
  kind : GKind := .std
  pattern : Option Node := none
  matchPattern : Option Node := none
  eqClassRel : Option Node := none
  childTypes : Array Int := #[]
  children : Array Nat := #[]
  childIndex : Array Nat := #[]
  next : Option Nat := none
  cg : Option CGKind := none
  activeAdd : Bool := true
  independent : Bool := false
  -- the round's state
  needsReset : Bool := true
  eqClass : Option Node := none
  firstCand : Option Node := none
  currMatched : Option Node := none
  exclude : Array Node := #[]
  cgs : CGState := {}
  deriving Inhabited

/-- `InstMatchGeneratorSimple`: the match pattern (an atomic term whose
children are variables or ground), its polarity and the class it must be in
(or not), and the variable of each child. -/
structure Simple where
  op : Node
  pat : Node
  pol : Bool
  eqc : Option Node
  varNum : Array (Nat × Int)
  deriving Inhabited

inductive Root where
  | simple (s : Simple)
  | gen (root : Nat)
  deriving Inhabited

/-- A trigger (`Trigger`): its formula, its terms, the ground terms in them
(`d_groundTerms`), its match generator(s) and the inference of its
instances. -/
structure Trig where
  q : Node
  nodes : Array Node
  groundTerms : Array Node
  root : Root
  gens : Array Gen
  id : String
  deriving Inhabited

/-- The data of E-matching (`InstStrategyAutoGenTriggers`, `TriggerDatabase`):
the triggers (by creation, their index standing for cvc5's pointers), those of
each formula (single, multi; with whether active), the trigger terms of each
formula, its number of trigger variables, the formulas whose triggers were made,
the rounds counted, and the triggers processed in the round. -/
structure EmData where
  trigs : Array Trig := #[]
  trie : Std.HashMap (Key × List Key) Nat := {}
  agt : Std.HashMap Key (Array (Nat × Bool) × Array (Nat × Bool)) := {}
  patTerms : Std.HashMap Key (Array Node × Array Node) := {}
  numTrigVars : Std.HashMap Key Nat := {}
  made : Std.HashSet Key := {}
  counter : Std.HashMap Key Nat := {}
  processed : Std.HashSet (Key × Nat) := {}
  /-- The selection state of each formula (its variables, node numbering). -/
  sel : Std.HashMap Key Sel := {}
  /-- The triggers of the user patterns of each formula (`d_user_gen`). -/
  userGen : Std.HashMap Key (Array Nat) := {}
  /-- cvc5's random numbers (`Random::getRandom`). -/
  rng : MT := MT.cvc5
  deriving Inhabited

/-- The selection state of `q`: its variables, and the nodes of its body
numbered. -/
def selOf (em : EmData) (q : Node) : Sel :=
  match em.sel.get? ⟨q⟩ with
  | some s => s
  | none =>
    let vars := (quantVars q).zipIdx.foldl (fun m (v, i) => m.insert ⟨v⟩ i) {}
    -- the patterns are substituted first (`InstantiationEngine::registerQuantifier`)
    let ipl := q.getChildren[2]?
    let excluded := match ipl with
      | some l => l.getChildren.filterMap fun p =>
        if p.getKind == .INST_NO_PATTERN then p.getChildren[0]? else none
      | none => #[]
    let go : SelM Unit := do
      if let some l := ipl then numberBody l
      numberBody (quantBody q)
    (go.run { vars, excluded }).2

/-! ### Construction (`initialize`, `mkInstMatchGenerator`) -/

abbrev TBM := StateT (Array Gen) (StateT Sel M)

def liftSel (x : SelM α) : TBM α := fun gs => do
  let s ← get
  let (a, s) := x.run s
  set s
  return (a, gs)

def newGen (g : Gen) : TBM Nat := modifyGet fun gs => (gs.size, gs.push g)

/-- `getInstMatchGenerator` (no purified or relational generators). -/
def mkGen (pat : Node) : TBM Nat := newGen { pattern := some pat, matchPattern := some pat }

/-- `InstMatchGenerator::initialize`: the generator's match pattern, its
children and its candidate generator; its children are added to `gens`. -/
def initGen (g : Nat) (gens : Array Nat) : TBM (Array Nat) := do
  let gen := (← get)[g]!
  if gen.kind == .multi then return gens ++ gen.children
  let some pat := gen.pattern | return gens
  let mut pattern := pat
  let mut mp := gen.matchPattern.getD pat
  if mp.getKind == .NOT then mp := mp.getChildren[0]!
  let mut eqRel : Option Node := none
  let mcs := mp.getChildren
  let bothVars ← if mp.getKind == .EQUAL then
      pure ((← liftSel (isVarOf mcs[0]!)) && (← liftSel (isVarOf mcs[1]!)))
    else pure false
  if pattern.getKind == .NOT && bothVars then pure ()
  else if mp.getKind == .EQUAL || mp.getKind == .GEQ then
    for i in [0, 1] do
      let m := mcs[i]!
      let mo := mcs[1 - i]!
      if (← liftSel (hasIC m)) && (!(← liftSel (hasIC mo)) || (← liftSel (isVarOf mo))) then
        if i == 1 then
          pattern := if mp.getKind == .GEQ then Node.notNode (Node.mkNode .GT #[m, mo])
            else Node.mkNode mp.getKind #[m, mo]
        eqRel := some mo
        mp := m
        break
  let op ← (getMatchOperator mp : M _)
  let mut childTypes : Array Int := #[]
  let mut children : Array Nat := #[]
  let mut childIndex : Array Nat := #[]
  if let some v ← liftSel (varNum mp) then childTypes := #[v]
  else
    let cs := mp.getChildren
    for i in [0:cs.size] do
      let c := cs[i]!
      if ← liftSel (hasIC c) then
        if let some v ← liftSel (varNum c) then childTypes := childTypes.push v
        else
          let cg ← mkGen c
          children := children.push cg
          childIndex := childIndex.push i
          childTypes := childTypes.push (-2)
      else childTypes := childTypes.push (-1)
  let mut cg : Option CGKind := none
  if isAtomicTriggerKind mp.getKind then
    if let some op := op then
      if pattern.getKind == .NOT && pattern.getChildren[0]!.getKind == .EQUAL then
        cg := some (.qe op (eqRel.toList.toArray))
        eqRel := none
      else cg := some (.qe op #[])
  else if (← liftSel (varNum mp)).isSome then cg := some (.all mp.typeHint)
  else if mp.getKind == .EQUAL then
    if pattern.getKind == .NOT then cg := some (.litDeq .EQUAL mp.getChildren[0]!.typeHint)
  modify fun gs => gs.modify g fun gen =>
    { gen with pattern := some pattern, matchPattern := some mp, eqClassRel := eqRel,
               childTypes, children, childIndex, cg }
  return gens ++ children

/-- `mkInstMatchGenerator` on the patterns `pats` (some with their generator
made already): each pattern's generator and their children, initialized and
chained (`d_next`) in order. -/
def mkGenChain (pats : Array Node) (init : Array (Node × Nat)) : TBM (Option Nat) := do
  let mut prev : Option Nat := none
  let mut oinit : Option Nat := none
  for p in pats do
    let i ← match init.find? (·.1 == p) with
      | some (_, g) => pure g
      | none => mkGen p
    if oinit.isNone then oinit := some i
    let mut gens := #[i]
    let mut counter := 0
    while counter < gens.size do
      let curr := gens[counter]!
      if let some pv := prev then modify fun gs => gs.modify pv fun g => { g with next := some curr }
      gens ← initGen curr gens
      prev := some curr
      counter := counter + 1
  return oinit

/-- `InstMatchGeneratorMultiLinear`: the patterns ordered (those sharing the
most bound variables first), each with a generator, the first independent. -/
def mkMultiLinear (pats : Array Node) : TBM Nat := do
  let mut vc : Array (Array Nat) := #[]
  for p in pats do vc := vc.push (← liftSel (fvOf p))
  let mut v2n : Std.HashMap Nat Nat := {}
  for fv in vc do
    for v in fv do v2n := v2n.insert v ((v2n.getD v 0) + 1)
  let mut ordered : Array Nat := #[]
  let mut bound : Std.HashSet Nat := {}
  while ordered.size < pats.size do
    let mut best : Option (Nat × Int × Int) := none
    for i in [0:pats.size] do
      if ordered.contains i then continue
      let mut s1 : Int := 0
      let mut s2 : Int := 0
      for v in vc[i]! do
        if bound.contains v then s1 := s1 + 1
        else if v2n.getD v 0 > 1 then s2 := s2 + 1
      match best with
      | none => best := some (i, s1, s2)
      | some (_, m1, m2) => if s1 > m1 || (s1 == m1 && s2 > m2) then best := some (i, s1, s2)
    let some (i, _, _) := best | break
    for v in vc[i]! do bound := bound.insert v
    ordered := ordered.push i
  let mut children : Array Nat := #[]
  for k in [0:ordered.size] do
    let c ← mkGen pats[ordered[k]!]!
    if k == 0 then modify fun gs => gs.modify c fun g => { g with independent := true }
    children := children.push c
  newGen { kind := .multi, children }

/-- `mkInstMatchGeneratorMulti`: the head, its children's generators chained
after it. -/
def mkMultiGen (pats : Array Node) : TBM Nat := do
  let h ← mkMultiLinear pats
  let gens ← initGen h #[]
  let mut init : Array (Node × Nat) := #[]
  let mut patsn : Array Node := #[]
  for g in gens do
    let p := ((← get)[g]!).matchPattern.getD default
    patsn := patsn.push p
    init := init.push (p, g)
  let nx ← mkGenChain patsn init
  modify fun gs => gs.modify h fun g => { g with next := nx }
  return h

/-- The ground terms in a trigger term (`ensureGroundTermPreprocessed`, with
the preprocessing of terms the identity), in the order cvc5 meets them. -/
def groundTermsOf (n : Node) : SelM (Array Node) := do
  let mut gts : Array Node := #[]
  let mut visited : Std.HashSet Key := {}
  let mut visit : Array Node := #[n]
  while !visit.isEmpty do
    let cur := visit.back!
    visit := visit.pop
    if visited.contains ⟨cur⟩ then continue
    visited := visited.insert ⟨cur⟩
    if cur.getChildren.isEmpty then continue
    if !(← hasIC cur) then
      gts := gts.push cur
      continue
    visit := visit ++ cur.getChildren
  return gts

def liftS (x : SelM α) : StateT Sel M α := fun s => pure (x.run s)

/-- `Trigger::Trigger`: a simple trigger's generator, or that of a single or
multi-trigger. -/
def mkTrig (q : Node) (nodes : Array Node) : StateT Sel M Trig := do
  let mut gts : Array Node := #[]
  for n in nodes do
    for g in ← liftS (groundTermsOf n) do
      gts := gts.push g
  if nodes.size == 1 then
    let n := nodes[0]!
    if ← liftS (isSimpleTrigger n) then
      let (pol, n1) := if n.getKind == Kind.NOT then (false, n.getChildren[0]!) else (true, n)
      let mut mp := n1
      let mut eqc : Option Node := none
      if mp.getKind == Kind.EQUAL then
        eqc := some mp.getChildren[1]!
        mp := mp.getChildren[0]!
      let cs := mp.getChildren
      let mut vn : Array (Nat × Int) := #[]
      for i in [0:cs.size] do
        if ← liftS (isVarOf cs[i]!) then
          let v ← liftS (varNum cs[i]!)
          vn := vn.push (i, match v with | some v => (v : Int) | none => -1)
      let op ← (getMatchOperator mp : M _)
      return { q, nodes, groundTerms := gts, gens := #[], id := "QUANTIFIERS_INST_E_MATCHING_SIMPLE",
               root := .simple { op := op.getD mp, pat := mp, pol, eqc, varNum := vn } }
    let (r, gens) ← (mkGenChain #[n] #[]).run #[]
    return { q, nodes, groundTerms := gts, gens, id := "QUANTIFIERS_INST_E_MATCHING",
             root := .gen (r.getD 0) }
  let (r, gens) ← (mkMultiGen nodes).run #[]
  return { q, nodes, groundTerms := gts, gens, id := "QUANTIFIERS_INST_E_MATCHING_MTL", root := .gen r }

/-- `mkTriggerTerms`: the terms of `nodes` needed to bind `nvars` variables,
in order, without those whose variables the others bind. -/
def mkTriggerTerms (nodes : Array Node) (nvars : Nat) : SelM (Option (Array Node)) := do
  let mut vc : Array (Array Nat) := #[]
  for p in nodes do vc := vc.push (← fvOf p)
  let mut vars : Std.HashSet Nat := {}
  let mut tr : Array Nat := #[]
  let mut patterns : Std.HashMap Nat (Array Nat) := {}
  for i in [0:nodes.size] do
    let mut found := false
    for v in vc[i]! do
      if !vars.contains v then
        vars := vars.insert v
        found := true
    if found then
      tr := tr.push i
      for v in vc[i]! do patterns := patterns.insert v ((patterns.getD v #[]).push i)
    if vars.size == nvars then break
  if vars.size < nvars then return none
  let mut k := 0
  while k < tr.size do
    let i := tr[k]!
    let keep := vc[i]!.any fun v => (patterns.getD v #[]).size == 1
    if !keep then
      for v in vc[i]! do patterns := patterns.modify v (·.erase i)
      tr := tr.eraseIdx! k
    else k := k + 1
  return some (tr.map (nodes[·]!))

end Telos.Solver.Quant
