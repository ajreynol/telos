import Telos.Solver.Theory.QuantState

/-!
# Conflict-based instantiation

A port of cvc5's `QuantConflictFind` (`src/theory/quantifiers/
quant_conflict_find.cpp`), `cbqi-mode=prop-eq`: for each asserted quantified
formula, the matches of its body against the equality engine that make it
false (a conflicting instance, `QUANTIFIERS_INST_CBQI_CONFLICT`) or, failing
those, that propagate an equality (`QUANTIFIERS_INST_CBQI_PROP`).

The body is a tree of match generators (`MatchGen`), kept here as an array per
quantified formula (`QInfo.mgs`), with their static parts (built when the
formula is registered) apart from those of a round (`MGDyn`). cvc5's ordered
maps (`std::map` by node id or by index) are sorted arrays, so that their
iteration follows cvc5's.

This is the procedure with instantiation evaluation off (`ieval=off`): the
match is checked by the entailment checks of `isTConstraintSpurious`.
-/

namespace Telos.Solver.Quant

/-! ## Sorted maps -/

/-- The value of `k` in a map sorted by key. -/
def amGet? [BEq α] (m : Array (α × β)) (k : α) : Option β := (m.find? (·.1 == k)).map (·.2)

/-- `m` with `k ↦ v`, kept sorted by `lt`. -/
def amSet [BEq α] (lt : α → α → Bool) (m : Array (α × β)) (k : α) (v : β) : Array (α × β) :=
  match m.findIdx? (·.1 == k) with
  | some i => m.set! i (k, v)
  | none =>
    let i := (m.findIdx? fun (k', _) => lt k k').getD m.size
    m.insertIdx! i (k, v)

def amErase [BEq α] (m : Array (α × β)) (k : α) : Array (α × β) := m.filter (·.1 != k)

def natLt (a b : Nat) : Bool := a < b

/-! ## Match generators -/

inductive MGType where
  | invalid | ground | pred | eq | var | boolVar | formula | tsym | tconstraint
  deriving BEq, Inhabited

/-- The static part of a match generator. -/
structure MGStatic where
  type : MGType := .invalid
  n : Node := Node.mkTrue
  typeNot : Bool := false
  children : Array Nat := #[]
  childrenOrder : Array Nat := #[]
  /-- `d_qni_var_num`: the variable at each index (0 the term, `i` its argument
  `i - 1`). -/
  qniVarNum : Array (Nat × Nat) := #[]
  /-- `d_qni_gterm`: the ground term at each index. -/
  qniGterm : Array (Nat × Node) := #[]
  qniSize : Nat := 0
  deriving Inhabited

/-- The part of a match generator of a round. -/
structure MGDyn where
  tgt : Bool := false
  tgtOrig : Bool := false
  wasSet : Bool := false
  childCounter : Int := -1
  useChildren : Bool := true
  /-- `d_qn`: the tries matched so far (`none` for cvc5's `nullptr`). -/
  qn : Array (Option Trie) := #[]
  /-- `d_qni`: the position in each trie's children. -/
  qni : Array Nat := #[]
  qniBound : Array (Nat × Nat) := #[]
  qniBoundCons : Array (Nat × Node) := #[]
  qniBoundConsVar : Array (Nat × Nat) := #[]
  binding : Bool := false
  bindingIt : Nat := 0
  groundEval : Array (Nat × Node) := #[]
  deriving Inhabited

/-- The static information of a quantified formula (`QuantInfo`). -/
structure QInfo where
  q : Node
  nvars : Nat
  vars : Array Node := #[]
  varNum : Std.HashMap Key Nat := {}
  varTypes : Array (Option TypeNode) := #[]
  extraVar : Array Node := #[]
  tsymVars : Array Nat := #[]
  /-- `d_var_mg`, sorted by variable. -/
  varMg : Array (Nat × Nat) := #[]
  /-- `d_var_rel_dom`: by variable, by operator (in node order), the argument
  positions. -/
  varRelDom : Array (Nat × Array (Node × Array Nat)) := #[]
  mgs : Array MGStatic := #[]
  root : Nat := 0
  registered : Std.HashSet Key := {}
  deriving Inhabited

namespace QInfo

def isVar (qi : QInfo) (n : Node) : Bool := qi.varNum.contains ⟨n⟩
def getVarNum (qi : QInfo) (n : Node) : Option Nat := qi.varNum.get? ⟨n⟩
def numVars (qi : QInfo) : Nat := qi.vars.size
def valid (qi : QInfo) : Bool := qi.mgs[qi.root]!.type != .invalid

end QInfo

/-- `isHandledUfTerm`. -/
def isHandledUfTerm (n : Node) : Bool := isAtomicTriggerKind n.getKind

/-- `QuantPhaseReq::getPolarity`. -/
def getPolarity (n : Node) (child : Nat) (hasPol pol : Bool) : Bool × Bool :=
  match n.getKind with
  | .AND | .OR => (hasPol, pol)
  | .IMPLIES => (hasPol, if child == 0 then !pol else pol)
  | .NOT => (hasPol, !pol)
  | .ITE => (child != 0 && hasPol, pol)
  | .FORALL => (child == 1 && hasPol, pol)
  | _ => (false, false)

/-- `QuantPhaseReq::getEntailPolarity`. -/
def getEntailPolarity (n : Node) (child : Nat) (hasPol pol : Bool) : Bool × Bool :=
  match n.getKind with
  | .AND | .OR => (hasPol && pol != (n.getKind == .OR), pol)
  | .IMPLIES => (hasPol && !pol, if child == 0 then !pol else pol)
  | .NOT => (hasPol, !pol)
  | _ => (false, false)

/-! ### Building the information of a formula -/

abbrev BM := StateT QInfo M

def addVar (n : Node) : BM Unit :=
  modify fun qi => { qi with varNum := qi.varNum.insert ⟨n⟩ qi.vars.size, vars := qi.vars.push n,
                             varTypes := qi.varTypes.push n.typeHint }

mutual
  /-- `QuantInfo::registerNode`. -/
  partial def registerNode (n : Node) (hasPol pol : Bool) (beneathQuant : Bool := false) : BM Unit := do
    if (← get).registered.contains ⟨n⟩ then return
    modify fun qi => { qi with registered := qi.registered.insert ⟨n⟩ }
    let cs := n.getChildren
    if n.getKind == .FORALL then return ← registerNode cs[1]! hasPol pol true
    if !isBoolConnectiveTerm n then
      if hasBoundVar n then
        if n.getKind == .EQUAL then
          for c in cs do flatten c beneathQuant
        else if isHandledUfTerm n then flatten n beneathQuant
        else if n.getKind == .ITE then
          flatten cs[1]! beneathQuant
          flatten cs[2]! beneathQuant
          registerNode cs[0]! false pol beneathQuant
    else
      for i in [0:cs.size] do
        let (hp, p) := getPolarity n i hasPol pol
        registerNode cs[i]! hp p beneathQuant

  /-- `QuantInfo::flatten`. -/
  partial def flatten (n : Node) (beneathQuant : Bool) : BM Unit := do
    if !hasBoundVar n || (← get).isVar n then return
    addVar n
    if n.getKind == .ITE then registerNode n false false
    else if let .boundVar .. := n then modify fun qi => { qi with extraVar := qi.extraVar.push n }
    else for c in n.getChildren do flatten c beneathQuant
end

/-- Add a match generator; its index. -/
def pushMg (m : MGStatic) : BM Nat :=
  modifyGet fun qi => (qi.mgs.size, { qi with mgs := qi.mgs.push m })

/-- The `MatchGen` constructor: its index. -/
partial def mkMatchGen (n : Node) (isVarGen : Bool) : BM Nat := do
  let qi ← get
  if isVarGen then
    if n.getKind == .ITE then return ← pushMg { type := .invalid, n }
    let vn := (qi.getVarNum n).get!
    let mut vnum : Array (Nat × Nat) := #[(0, vn)]
    let mut gterm : Array (Nat × Node) := #[]
    let cs := n.getChildren
    for j in [0:cs.size] do
      match qi.getVarNum cs[j]! with
      | some v => vnum := vnum.push (j + 1, v)
      | none => gterm := gterm.push (j + 1, cs[j]!)
    return ← pushMg { type := if isHandledUfTerm n then .var else .tsym, n, qniVarNum := vnum,
                      qniGterm := gterm, qniSize := cs.size + 1 }
  if !hasBoundVar n then return ← pushMg { type := .ground, n }
  let (d, tnot) := match n with
    | .app (.kind .NOT) #[a] => (a, true)
    | _ => (n, false)
  if isBoolConnectiveTerm d then
    let cs := d.getChildren
    let mut kids : Array Nat := #[]
    let mut ok := true
    for i in [0:cs.size] do
      if d.getKind != .FORALL || i == 1 then
        let c ← mkMatchGen cs[i]! false
        if (← get).mgs[c]!.type == .invalid then ok := false; break
        kids := kids.push c
    if !ok then return ← pushMg { type := .invalid, n := d, typeNot := tnot }
    return ← pushMg { type := .formula, n := d, typeNot := tnot, children := kids }
  if isHandledUfTerm d then return ← pushMg { type := .pred, n := d, typeNot := tnot }
  if let .boundVar .. := d then return ← pushMg { type := .boolVar, n := d, typeNot := tnot }
  if d.getKind == .EQUAL then
    let cs := d.getChildren
    let mut gterm : Array (Nat × Node) := #[]
    for i in [0:cs.size] do
      if !hasBoundVar cs[i]! then gterm := gterm.push (i, cs[i]!)
    return ← pushMg { type := .eq, n := d, typeNot := tnot, qniGterm := gterm }
  pushMg { type := .invalid, n := d, typeNot := tnot }

/-- `collectBoundVar`. -/
partial def collectBoundVar (qi : QInfo) (n : Node) (acc : Array Nat) (visited : Std.HashSet Key) :
    Array Nat × Std.HashSet Key :=
  if visited.contains ⟨n⟩ then (acc, visited) else
  let visited := visited.insert ⟨n⟩
  let acc := match qi.getVarNum n with
    | some v => if acc.contains v then acc else acc.push v
    | none => acc
  n.getChildren.foldl (fun (acc, vis) c => collectBoundVar qi c acc vis) (acc, visited)

/-- `determineVariableOrder` of the generator `g`. -/
partial def determineVariableOrder (g : Nat) (bvars : Array Nat) : BM (Array Nat) := do
  let qi ← get
  let m := qi.mgs[g]!
  let isComm := m.type == .formula && (m.n.getKind == .OR || m.n.getKind == .AND || m.n.getKind == .EQUAL)
  let mut bvars := bvars
  let mut order : Array Nat := #[]
  if isComm then
    let nc := m.children.size
    let cvars : Array (Array Nat) := m.children.map fun c => (collectBoundVar qi qi.mgs[c]!.n #[] {}).1
    let mut vuCount : Array Int := cvars.map fun cv => (cv.filter (!bvars.contains ·)).size
    let mut assigned : Array Bool := Array.replicate nc false
    while order.size != nc do
      let mut minScore : Int := -1
      let mut minIdx : Nat := 0
      for i in [0:nc] do
        if !assigned[i]! then
          let score := vuCount[i]!
          if minScore == -1 || score < minScore then
            minScore := score
            minIdx := i
      order := order.push minIdx
      assigned := assigned.set! minIdx true
      bvars ← determineVariableOrder m.children[minIdx]! bvars
      if vuCount[minIdx]! > 0 then
        for v in cvars[minIdx]! do
          if !bvars.contains v then
            for j in [0:nc] do
              if cvars[j]!.contains v then vuCount := vuCount.set! j (vuCount[j]! - 1)
            bvars := bvars.push v
  else
    for i in [0:m.children.size] do
      order := order.push i
      bvars ← determineVariableOrder m.children[i]! bvars
      for v in (collectBoundVar qi qi.mgs[m.children[i]!]!.n #[] {}).1 do
        if !bvars.contains v then bvars := bvars.push v
  modify fun qi => { qi with mgs := qi.mgs.modify g fun m => { m with childrenOrder := order } }
  return bvars

/-- `getPropagateVars`, and the formulas of each operator
(`d_func_rel_dom`). -/
partial def getPropagateVars (n : Node) (pol : Bool) (vars : Array Node) (visited : Std.HashSet Key) :
    BM (Array Node × Std.HashSet Key) := do
  if visited.contains ⟨n⟩ then return (vars, visited)
  let mut visited := visited.insert ⟨n⟩
  let mut vars := vars
  let mut recur := true
  if (← get).isVar n then
    vars := vars.push n
  else if isBoolConnectiveTerm n then
    recur := (getEntailPolarity n 0 true pol).1
  if recur then
    for c in n.getChildren do
      (vars, visited) ← getPropagateVars c pol vars visited
  return (vars, visited)

/-- The information of `q` (the `QuantInfo` constructor), and the operators
of its propagating variables (for `d_func_rel_dom`). -/
def mkQInfo (q : Node) : M (QInfo × Array Node) := do
  let vs := quantVars q
  let qi : QInfo := { q, nvars := vs.size }
  let act : BM (Array Node) := do
    for v in vs do addVar v
    let body := quantBody q
    registerNode body true true
    let root ← mkMatchGen body false
    modify fun qi => { qi with root }
    if (← get).valid then
      let nv := (← get).vars.size
      for j in [vs.size:nv] do
        let v := (← get).vars[j]!
        if let .boundVar .. := v then continue
        let isTsym := !isHandledUfTerm v && v.getKind != .ITE
        if isTsym then
          modify fun qi => { qi with tsymVars := qi.tsymVars.push j }
          -- (no t-constraints: the formula is not handled)
          modify fun qi => { qi with mgs := qi.mgs.modify qi.root fun m => { m with type := .invalid, children := #[] } }
          break
        let g ← mkMatchGen v true
        if (← get).mgs[g]!.type == .invalid then
          modify fun qi => { qi with mgs := qi.mgs.modify qi.root fun m => { m with type := .invalid, children := #[] } }
          break
        modify fun qi => { qi with varMg := amSet natLt qi.varMg j g }
        let _ ← determineVariableOrder g #[]
      if (← get).valid then
        let _ ← determineVariableOrder (← get).root #[]
    if !(← get).valid then return #[]
    let (pvars, _) ← getPropagateVars body false #[] {}
    let mut fops : Array Node := #[]
    for v in pvars do
      let some f ← (getMatchOperator v : M _) | continue
      fops := fops.push f
      let cs := v.getChildren
      for k in [0:cs.size] do
        if let some vn := (← get).getVarNum cs[k]! then
          let c ← read
          modify fun qi =>
            let byOp := (amGet? qi.varRelDom vn).getD #[]
            let ks := (amGet? byOp f).getD #[]
            let ks := if ks.contains k then ks else ks.push k
            { qi with varRelDom := amSet natLt qi.varRelDom vn (amSet c.lt byOp f ks) }
    return fops
  let (fops, qi) ← act.run qi
  return (qi, fops)

/-! ### Matching -/

/-- The dynamic information of a formula in a round. -/
structure QDyn where
  match_ : Array (Option Node)
  matchTerm : Array (Option Node)
  varsSet : Std.HashSet Nat := {}
  currVarDeq : Array (Nat × Array (Node × Nat)) := #[]
  instMatch : Array (Option Node)
  mg : Array MGDyn
  unassigned : Array Nat := #[]
  unassignedTn : Array (Option TypeNode) := #[]
  unassignedNvar : Nat := 0
  unaIndex : Nat := 0
  unaEqcCount : Array Int := #[]
  deriving Inhabited

/-- What a round of matching sees: the formula, the classes by type, and the
effort. -/
structure QEnv where
  qi : QInfo
  eqcs : Std.HashMap (Option TypeNode) (Array Node)
  conflictEffort : Bool

structure QSt where
  d : QDyn
  /-- `d_irr_func` found in this formula. -/
  irrFunc : Array Node := #[]

abbrev QM := ReaderT QEnv (StateT QSt M)

def qi : QM QInfo := return (← read).qi
def dyn : QM QDyn := return (← get).d
def modD (f : QDyn → QDyn) : QM Unit := modify fun s => { s with d := f s.d }
def mgS (g : Nat) : QM MGStatic := return (← qi).mgs[g]!
def mgD (g : Nat) : QM MGDyn := return (← dyn).mg[g]!
def modMg (g : Nat) (f : MGDyn → MGDyn) : QM Unit := modD fun d => { d with mg := d.mg.modify g f }
def ctx : QM Ctx := liftM (read : M Ctx)
def lt : QM (Node → Node → Bool) := return (← ctx).lt

def getVar (v : Nat) : QM Node := return (← qi).vars[v]!

/-- `getCurrentRepVar`. -/
partial def getCurrentRepVar (v : Nat) : QM Nat := do
  match (← dyn).match_[v]! with
  | some m =>
    match (← qi).getVarNum m with
    | some w => getCurrentRepVar w
    | none => return v
  | none => return v

/-- `getCurrentValue`. -/
partial def getCurrentValue (n : Node) : QM Node := do
  match (← qi).getVarNum n with
  | none => return n
  | some v =>
    match (← dyn).match_[v]! with
    | none => return n
    | some m => getCurrentValue m

/-- `getCurrentExpValue`. -/
def getCurrentExpValue (n : Node) : QM Node := do
  match (← qi).getVarNum n with
  | none => return n
  | some v =>
    match (← dyn).match_[v]! with
    | none => return n
    | some m =>
      match (← dyn).matchTerm[v]! with
      | none => getCurrentValue m
      | some mt => return mt

/-- `getCurrentCanBeEqual`. -/
def getCurrentCanBeEqual (v : Nat) (n : Node) (chDiseq : Bool := false) : QM Bool := do
  let some deqs := amGet? (← dyn).currVarDeq v | return true
  for (dn, _) in deqs do
    let cv ← getCurrentValue dn
    if cv == n then return false
    if chDiseq && !(← qi).isVar n && !(← qi).isVar cv then
      if !(← ctx).areDisequal n cv then return false
  return true

/-- `InstMatch::set`, without instantiation evaluation. -/
def instMatchSet (i : Nat) (n : Node) : QM Bool := do
  match (← dyn).instMatch[i]! with
  | some m => return (← ctx).areEqual m n
  | none =>
    modD fun d => { d with instMatch := d.instMatch.set! i (some n) }
    return true

/-- `setMatch`. -/
def setMatch (v : Nat) (n : Node) (isGroundRep isGround : Bool) : QM Bool := do
  if !(← getCurrentCanBeEqual v n) then return false
  if isGroundRep then
    if let some byOp := amGet? (← qi).varRelDom v then
      for (f, ks) in byOp do
        for k in ks do
          if !(← (inRelevantDomain f k n : M _)) then return false
  let vv ← getVar v
  if isGround then
    if let .boundVar .. := vv then
      if v < (← qi).nvars then
        if (← dyn).instMatch[v]!.isSome then
          modD fun d => { d with instMatch := d.instMatch.set! v none }
        if !(← instMatchSet v n) then return false
      modD fun d => { d with varsSet := d.varsSet.insert v }
  modD fun d => { d with match_ := d.match_.set! v (some n) }
  return true

/-- `unsetMatch`. -/
def unsetMatch (v : Nat) : QM Unit := do
  let vv ← getVar v
  if let .boundVar .. := vv then
    if (← dyn).varsSet.contains v then
      modD fun d => { d with varsSet := d.varsSet.erase v }
      if v < (← qi).nvars then
        modD fun d => { d with instMatch := d.instMatch.set! v none }
  modD fun d => { d with match_ := d.match_.set! v none }

/-- `addConstraint` (the internal form). -/
partial def addConstraintI (v : Nat) (n : Node) (vn : Option Nat) (polarity doRemove : Bool) : QM Int := do
  let l ← lt
  if polarity then
    if vn == some v then return 0
    if doRemove then
      if let some w := vn then
        if (← dyn).match_[w]! == some (← getVar v) then
          return ← addConstraintI w (← getVar v) (some v) true true
        else
          if let some deqs := amGet? (← dyn).currVarDeq w then
            let deqs := deqs.filter (·.2 != v)
            modD fun d => { d with currVarDeq := amSet natLt d.currVarDeq w deqs }
      unsetMatch v
      return 1
    let mut n := n
    let mut isGround := false
    match vn with
    | some w =>
      if (← dyn).match_[v]!.isNone then
        let alreadySet := (← dyn).match_[w]!.isSome
        if let some deqs := amGet? (← dyn).currVarDeq v then
          let mut cvd := (amGet? (← dyn).currVarDeq w).getD #[]
          for (dn, _) in deqs do
            let dv ← getCurrentValue dn
            if !alreadySet then
              if (amGet? cvd dv).isNone then cvd := amSet l cvd dv v
            else if (← dyn).match_[w]! == some dv then
              return -1
          if !alreadySet then
            modD fun d => { d with currVarDeq := amSet natLt d.currVarDeq w cvd }
        if alreadySet then n ← getCurrentValue n
      else
        if (← dyn).match_[w]!.isNone then
          return ← addConstraintI w (← getVar v) (some v) true false
        return if (← dyn).match_[v]! == (← dyn).match_[w]! then 0 else -1
    | none =>
      if (← dyn).match_[v]!.isNone then isGround := true
      else return if (← dyn).match_[v]! == some n then 0 else -1
    return if ← setMatch v n false isGround then 1 else -1
  else
    if vn == some v then return -1
    if doRemove then
      let deqs := ((amGet? (← dyn).currVarDeq v).getD #[])
      modD fun d => { d with currVarDeq := amSet natLt d.currVarDeq v (amErase deqs n) }
      return 1
    let deqs := (amGet? (← dyn).currVarDeq v).getD #[]
    if (amGet? deqs n).isNone then
      if let some m := (← dyn).match_[v]! then
        let nv ← getCurrentValue n
        if nv == m then return -1
      modD fun d => { d with currVarDeq := amSet natLt d.currVarDeq v (amSet l deqs n v) }
      return 1
    return 0

/-- `isConstrainedVar`. -/
def isConstrainedVar (v : Nat) : QM Bool := do
  let d ← dyn
  if let some deqs := amGet? d.currVarDeq v then
    if !deqs.isEmpty then return true
  let vv ← getVar v
  if d.match_.any (· == some vv) then return true
  return d.currVarDeq.any fun (_, deqs) => deqs.any (·.1 == vv)

def varMgOf (v : Nat) : QM (Option Nat) := return amGet? (← qi).varMg v

/-! #### Match generators in a round -/

/-- `MatchGen::reset_round`. -/
partial def mgResetRound (g : Nat) : QM Bool := do
  modMg g fun m => { m with wasSet := false }
  for c in (← mgS g).children do
    if !(← mgResetRound c) then return false
  let s ← mgS g
  let c ← ctx
  if s.type == .ground then
    for i in [0, 1] do
      if ← (isEntailed s.n {} false (i == 0) : M _) then
        modMg g fun m => { m with groundEval := amSet natLt m.groundEval 0 (Node.mkBool (i == 0)) }
  else if s.type == .eq then
    let cs := s.n.getChildren
    for i in [0:cs.size] do
      if !hasBoundVar cs[i]! then
        let t ← (getEntailedTerm cs[i]! {} false : M _)
        modMg g fun m => { m with groundEval := amSet natLt m.groundEval i (t.getD cs[i]!) }
  let _ := c
  modMg g fun m => { m with qniBoundCons := #[], qniBoundConsVar := #[], qniBound := #[] }
  return true

mutual
  /-- `MatchGen::reset`. -/
  partial def mgReset (g : Nat) (tgt : Bool) : QM Unit := do
    let s ← mgS g
    let t := if s.typeNot then !tgt else tgt
    modMg g fun m => { m with tgt := t, qn := #[], qni := #[], qniBound := #[], childCounter := -1,
                              useChildren := true, tgtOrig := t }
    let q ← qi
    let c ← ctx
    let complete := (← dyn).varsSet.size == q.nvars + q.extraVar.size
    if s.type == .invalid then
      modMg g fun m => { m with useChildren := false }
    else if s.type == .ground then
      let ge := amGet? (← mgD g).groundEval 0
      modMg g fun m => { m with useChildren := false }
      if ge == some (Node.mkBool t) then modMg g fun m => { m with childCounter := 0 }
    else if complete then
      modMg g fun m => { m with useChildren := false, childCounter := 0 }
    else if s.type == .boolVar then
      let n ← getCurrentValue s.n
      match q.getVarNum n with
      | none =>
        if ← (isEntailed n {} false t : M _) then modMg g fun m => { m with childCounter := 0 }
      | some vnn =>
        let vn ← getCurrentRepVar vnn
        modMg g fun m => { m with qniBound := amSet natLt m.qniBound 0 vn }
        let _ ← setMatch vn (Node.mkBool t) false true
        modMg g fun m => { m with childCounter := 0 }
      if (← mgD g).childCounter == 0 then modMg g fun m => { m with qn := m.qn.push none }
    else if s.type == .var then
      let some f ← (getMatchOperator s.n : M _) | pure ()
      let trie ← (computeUfEqcTerms f : M _)
      if trie.data.isEmpty then
        modify fun st => { st with irrFunc := st.irrFunc.push f }
      else modMg g fun m => { m with qn := m.qn.push (some trie) }
    else if s.type == .tsym || s.type == .tconstraint then
      for (i, v) in s.qniVarNum do
        let rv ← getCurrentRepVar v
        if (← dyn).match_[rv]!.isNone then modMg g fun m => { m with qniBound := amSet natLt m.qniBound i rv }
      modMg g fun m => { m with qn := m.qn.push none }
    else if s.type == .pred || s.type == .eq then
      let mut nn : Array Node := #[]
      let mut vn : Array (Option Nat) := #[]
      let mut t' := t
      if s.type == .pred then
        let n0 ← getCurrentValue s.n
        nn := #[n0, Node.mkBool t]
        let v0 ← match q.getVarNum n0 with
          | some w => some <$> getCurrentRepVar w
          | none => pure none
        vn := #[v0, none]
        t' := true
        modMg g fun m => { m with tgt := true }
      else
        let cs := s.n.getChildren
        for i in [0, 1] do
          let nc := (amGet? s.qniGterm i).getD cs[i]!
          let ni ← getCurrentValue nc
          nn := nn.push ni
          vn := vn.push (← match q.getVarNum ni with
            | some w => some <$> getCurrentRepVar w
            | none => pure none)
      let mut success := false
      if vn[0]!.isNone && vn[1]!.isNone then
        if t' then success := nn[0]! == nn[1]!
        else if (← read).conflictEffort then success := c.areDisequal nn[0]! nn[1]!
        else success := nn[0]! != nn[1]!
      else
        if vn[1]!.isSome && vn[0]!.isNone then
          nn := #[nn[1]!, nn[0]!]
          vn := #[vn[1]!, none]
        let addc ← addConstraintI vn[0]!.get! nn[1]! vn[1]! t' false
        success := addc != -1
        if addc == 1 then
          for i in [0, 1] do
            if let some w := vn[i]! then
              modMg g fun m => { m with qniBound := amSet natLt m.qniBound w w }
          modMg g fun m => { m with qniBoundCons := amSet natLt m.qniBoundCons vn[0]!.get! nn[1]!,
                                    qniBoundConsVar := match vn[1]! with
                                      | some w => amSet natLt m.qniBoundConsVar vn[0]!.get! w
                                      | none => m.qniBoundConsVar }
      if success then modMg g fun m => { m with qn := m.qn.push none }
    else
      -- a formula
      if s.children.isEmpty then modMg g fun m => { m with qn := m.qn.push none }
      else if t && s.n.getKind == .FORALL then pure ()
      else if s.n.getKind == .FORALL && (← read).conflictEffort then pure ()
      else
        modMg g fun m => { m with childCounter := 0 }
        mgReset (← getChild g 0) t
    modMg g fun m => { m with binding := false, wasSet := true }

  /-- The child at position `i` of the order. -/
  partial def getChild (g : Nat) (i : Nat) : QM Nat := do
    let s ← mgS g
    return s.children[s.childrenOrder[i]!]!

  /-- `MatchGen::doMatching`. -/
  partial def doMatching (g : Nat) : QM Bool := do
    let m ← mgD g
    if m.qn.isEmpty then return false
    if m.qn[0]!.isNone then
      modMg g fun m => { m with qn := #[] }
      return true
    let s ← mgS g
    let c ← ctx
    let rec loop (fuel : Nat) : QM Unit := do
      if fuel == 0 then return
      let m ← mgD g
      let mut invalidMatch := false
      if m.qn.size == m.qni.size + 1 then
        let index := m.qni.size
        let mut val : Option Node := none
        match amGet? s.qniVarNum index with
        | some v =>
          let repVar ← getCurrentRepVar v
          match (← dyn).match_[repVar]! with
          | some mv => val := some mv
          | none =>
            modMg g fun m => { m with qniBound := amSet natLt m.qniBound index repVar }
            let tr := m.qn[index]!.get!
            if h : 0 < tr.data.size then
              let (k, sub) := tr.data[0]
              modMg g fun m => { m with qni := m.qni.push 0 }
              if k.typeHint == (← qi).varTypes[repVar]! && (← setMatch repVar k true true) then
                if (← mgD g).qn.size < s.qniSize then
                  modMg g fun m => { m with qn := m.qn.push (some sub) }
              else invalidMatch := true
            else
              modMg g fun m => { m with qn := m.qn.pop }
        | none => val := amGet? s.qniGterm index
        if let some v := val then
          let vr := c.rep v
          let tr := m.qn[index]!.get!
          let (i, found) := Trie.search c.lt tr.data vr
          if found then
            modMg g fun m => { m with qni := m.qni.push i }
            if (← mgD g).qn.size < s.qniSize then
              modMg g fun m => { m with qn := m.qn.push (some tr.data[i]!.2) }
          else
            modMg g fun m => { m with qn := m.qn.pop }
      else
        let index := m.qni.size - 1
        let mut success := false
        match amGet? m.qniBound index with
        | some bv =>
          let ni := m.qni[index]! + 1
          modMg g fun m => { m with qni := m.qni.set! index ni }
          let tr := m.qn[index]!.get!
          if h : ni < tr.data.size then
            success := true
            let (k, sub) := tr.data[ni]
            if ← setMatch bv k true true then
              if (← mgD g).qn.size < s.qniSize then
                modMg g fun m => { m with qn := m.qn.push (some sub) }
            else invalidMatch := true
          else
            unsetMatch bv
            modD fun d => { d with matchTerm := d.matchTerm.set! bv none }
        | none => pure ()
        if !success then
          modMg g fun m => { m with qn := m.qn.pop, qni := m.qni.pop }
      let m ← mgD g
      if (!m.qn.isEmpty && m.qni.size != s.qniSize) || invalidMatch then loop (fuel - 1)
    loop 1000000
    let m ← mgD g
    if m.qni.size == s.qniSize then
      -- the term matched
      let mut tr := m.qn[0]!.get!
      for i in [0:m.qni.size] do
        tr := tr.data[m.qni[i]!]!.2
      let t := tr.data[0]!.1
      let v0 := (amGet? s.qniVarNum 0).get!
      modD fun d => { d with matchTerm := d.matchTerm.set! v0 (some t) }
      for (i, bv) in m.qniBound do
        if i > 0 then
          modD fun d => { d with matchTerm := d.matchTerm.set! bv (some t.getChildren[i - 1]!) }
    return !(← mgD g).qn.isEmpty

  /-- `MatchGen::getNextMatch`. -/
  partial def getNextMatch (g : Nat) : QM Bool := do
    let s ← mgS g
    let m ← mgD g
    if !m.useChildren then
      if m.childCounter == 0 then
        modMg g fun m => { m with childCounter := -1 }
        return true
      modMg g fun m => { m with wasSet := false }
      return false
    if s.type == .var || s.type == .eq || s.type == .pred || s.type == .boolVar ||
        s.type == .tconstraint || s.type == .tsym then
      let mut success := false
      let mut terminate := false
      repeat
        let mut doReset := false
        let mut doFail := false
        if !(← mgD g).binding then
          if ← doMatching g then
            modMg g fun m => { m with binding := true, bindingIt := 0 }
            doReset := true
          else
            success := false
            terminate := true
        else doFail := true
        if (← mgD g).binding then
          success := true
          repeat
            let m ← mgD g
            if !((success && m.bindingIt < m.qniBound.size) || doFail) then break
            let entry := m.qniBound[m.bindingIt]?
            let vmg ← match entry with
              | some (_, v) => if doFail then pure none else varMgOf v
              | none => pure none
            if doFail || (match entry with | some (i, _) => i != 0 && vmg.isSome | none => false) then
              let gm := match vmg with
                | some x => x
                | none => 0
              if doReset then mgReset gm true
              let next ← if doFail then pure false else getNextMatch gm
              if doFail || !next then
                repeat
                  let m ← mgD g
                  if m.bindingIt == 0 then
                    success := false
                  else
                    modMg g fun m => { m with bindingIt := m.bindingIt - 1 }
                  let m ← mgD g
                  let vmgs := (← qi).varMg
                  let cont := success && (match m.qniBound[m.bindingIt]? with
                    | some (i, v) => i == 0 || (amGet? vmgs v).isNone
                    | none => false)
                  if !cont then break
                doReset := false
                doFail := false
              else
                modMg g fun m => { m with bindingIt := m.bindingIt + 1 }
                doReset := true
            else
              modMg g fun m => { m with bindingIt := m.bindingIt + 1 }
              doReset := true
          if !success then
            modMg g fun m => { m with binding := false }
          else
            terminate := true
            if (← mgD g).bindingIt == 0 then modMg g fun m => { m with binding := false }
        if terminate then break
      if !success then
        if s.type == .eq || s.type == .pred then
          let m ← mgD g
          for (v, cn) in m.qniBoundCons do
            let w := amGet? m.qniBoundConsVar v
            let _ ← addConstraintI v cn w m.tgt true
          modMg g fun m => { m with qniBoundCons := #[], qniBoundConsVar := #[], qniBound := #[] }
        else
          for (_, v) in (← mgD g).qniBound do
            unsetMatch v
            modD fun d => { d with matchTerm := d.matchTerm.set! v none }
          modMg g fun m => { m with qniBound := #[] }
      modMg g fun m => { m with wasSet := success }
      return success
    if s.type == .formula then
      let mut success := false
      let m ← mgD g
      if m.childCounter < 0 then
        if m.childCounter < -1 then modMg g fun m => { m with childCounter := -1 }
        return false
      let k := s.n.getKind
      let nch := s.children.size
      let tgt := (← mgD g).tgt
      while !success && (← mgD g).childCounter >= 0 do
        let cc := (← mgD g).childCounter
        if k == .OR || k == .AND then
          if (k == .AND) == tgt then
            if ← getNextMatch (← getChild g cc.toNat) then
              if cc < (nch : Int) - 1 then
                modMg g fun m => { m with childCounter := cc + 1 }
                mgReset (← getChild g (cc + 1).toNat) tgt
              else success := true
            else modMg g fun m => { m with childCounter := cc - 1 }
          else
            if !(← getNextMatch (← getChild g cc.toNat)) then
              if cc < (nch : Int) - 1 then
                modMg g fun m => { m with childCounter := cc + 1 }
                mgReset (← getChild g (cc + 1).toNat) tgt
              else modMg g fun m => { m with childCounter := -1 }
            else success := true
        else if k == .EQUAL then
          let mut cc := cc
          if cc % 2 == 0 then
            if ← getNextMatch (← getChild g 0) then
              cc := cc + 1
              modMg g fun m => { m with childCounter := cc }
              mgReset (← getChild g 1) (cc == 1)
            else
              if cc == 0 then
                cc := 2
                modMg g fun m => { m with childCounter := 2 }
                mgReset (← getChild g 0) !tgt
              else
                cc := -1
                modMg g fun m => { m with childCounter := -1 }
          if cc >= 0 && cc % 2 == 1 then
            if ← getNextMatch (← getChild g 1) then success := true
            else modMg g fun m => { m with childCounter := cc - 1 }
        else if k == .ITE then
          let mut cc := cc
          if cc % 2 == 0 then
            let index1 := if cc == 4 then 1 else 0
            if ← getNextMatch (← getChild g index1) then
              cc := cc + 1
              modMg g fun m => { m with childCounter := cc }
              let which := if cc == 5 then 2 else (if tgt == (cc == 1) then 1 else 2)
              mgReset (← getChild g which) tgt
            else
              if cc == 4 then
                cc := -1
                modMg g fun m => { m with childCounter := -1 }
              else
                cc := cc + 2
                modMg g fun m => { m with childCounter := cc }
                mgReset (← getChild g (if cc == 2 then 0 else 1)) (if cc == 2 then !tgt else tgt)
          if cc >= 0 && cc % 2 == 1 then
            let index2 := if cc == 5 then 2 else (if tgt == (cc == 1) then 1 else 2)
            if ← getNextMatch (← getChild g index2) then success := true
            else modMg g fun m => { m with childCounter := cc - 1 }
        else if k == .FORALL then
          if ← getNextMatch (← getChild g cc.toNat) then success := true
          else modMg g fun m => { m with childCounter := -1 }
        else
          modMg g fun m => { m with childCounter := -1 }
      modMg g fun m => { m with wasSet := success }
      return success
    return false
end

/-- `isMatchSpurious`. -/
def isMatchSpurious : QM Bool := do
  let ce := (← read).conflictEffort
  for i in [0:(← qi).numVars] do
    if let some m := (← dyn).match_[i]! then
      if !(← getCurrentCanBeEqual i m ce) then return true
  return false

/-- `revertMatch`. -/
def revertMatch (assigned : Array Nat) : QM Unit := do
  for a in assigned do unsetMatch a

/-- `completeMatch` (no symbolic variables: the formula is not handled if it
has some). -/
partial def completeMatch (assigned : Array Nat) : QM (Bool × Array Nat) := do
  let q ← qi
  if (← dyn).varsSet.size == q.nvars + q.extraVar.size then return (true, assigned)
  let mut assigned := assigned
  -- the unassigned variables: those with a generator first
  let mut ua : Array Nat := #[]
  let mut ub : Array Nat := #[]
  for i in [0:q.numVars] do
    if (← dyn).match_[i]!.isNone then
      if (amGet? q.varMg i).isSome then ua := ua.push i else ub := ub.push i
      assigned := assigned.push i
  let un := ua ++ ub
  modD fun d => { d with unassigned := un, unassignedTn := un.map fun v => q.varTypes[v]!,
                         unassignedNvar := ua.size, unaEqcCount := #[], unaIndex := 0 }
  let mut success := true
  let mut doFail := false
  if !un.isEmpty then
    repeat
      let mut invalidMatch := false
      repeat
        let d ← dyn
        if !((success && d.unaIndex < d.unassigned.size) || invalidMatch || doFail) then break
        invalidMatch := false
        if !doFail && d.unaIndex == d.unaEqcCount.size then
          if d.unaIndex < d.unassignedNvar then
            let v := d.unassigned[d.unaIndex]!
            if !(← isConstrainedVar v) then
              modD fun d => { d with unaEqcCount := d.unaEqcCount.push (-1) }
            else
              mgReset (amGet? q.varMg v).get! true
              modD fun d => { d with unaEqcCount := d.unaEqcCount.push 0 }
          else
            modD fun d => { d with unaEqcCount := d.unaEqcCount.push 0 }
        else
          let mut failed := false
          if !doFail then
            if d.unaIndex < d.unassignedNvar then
              let v := d.unassigned[d.unaIndex]!
              if !(← isConstrainedVar v) then
                modD fun d => { d with unaIndex := d.unaIndex + 1 }
              else if ← getNextMatch (amGet? q.varMg v).get! then
                modD fun d => { d with unaIndex := d.unaIndex + 1 }
              else failed := true
            else
              let eqcs := ((← read).eqcs.get? d.unassignedTn[d.unaIndex]!).getD #[]
              let ci := d.unaEqcCount[d.unaIndex]!
              if ci < (eqcs.size : Int) then
                modD fun d => { d with unaEqcCount := d.unaEqcCount.set! d.unaIndex (ci + 1) }
                let v := d.unassigned[d.unaIndex]!
                if ← setMatch v eqcs[ci.toNat]! true true then
                  modD fun d => { d with matchTerm := d.matchTerm.set! v none, unaIndex := d.unaIndex + 1 }
                else invalidMatch := true
              else failed := true
          if doFail || failed then
            repeat
              if !doFail then
                modD fun d => { d with unaEqcCount := d.unaEqcCount.pop }
              else doFail := false
              if (← dyn).unaIndex == 0 then
                success := false
                break
              modD fun d => { d with unaIndex := d.unaIndex - 1 }
              let d ← dyn
              if d.unaEqcCount[d.unaIndex]! != -1 then break
      if success then doFail := true
      if !(success && (← isMatchSpurious)) then break
  if success then return (true, assigned)
  revertMatch assigned
  return (false, #[])

/-- `getMatch`. -/
def getMatch : QM (Array Node) := do
  let mut terms := #[]
  for i in [0:(← qi).nvars] do
    let rv ← getCurrentRepVar i
    let d ← dyn
    terms := terms.push ((d.matchTerm[rv]!.orElse fun _ => d.match_[rv]!).getD Node.mkTrue)
  return terms

/-- `isTConstraintSpurious`, without instantiation evaluation: the instance is
entailed false (conflict), or does not evaluate to `true` (propagation). -/
def isTConstraintSpurious (terms : Array Node) : QM Bool := do
  let q ← qi
  let mut subs : Subs := {}
  for i in [0:terms.size] do subs := subs.insert ⟨(quantVars q.q)[i]!⟩ terms[i]!
  for v in q.extraVar do subs := subs.insert ⟨v⟩ (← getCurrentExpValue v)
  if (← read).conflictEffort then
    if !(← (isEntailed (quantBody q.q) subs false false : M _)) then return true
  else
    let ev ← (evaluateTerm (quantBody q.q) subs false true : M _)
    match ev with
    | none => return true
    | some e => if e == Node.mkTrue then return true
  return (← get).d.match_.isEmpty && false

end Telos.Solver.Quant
