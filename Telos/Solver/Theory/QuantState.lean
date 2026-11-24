import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Core.Node.NodeOrder

/-!
# The state of the quantifiers engine

The state of cvc5's quantifiers engine (`src/theory/quantifiers/`), in the
configuration of safe mode (`docs/theory-engine-plan.md`, Stage 10): its
registry and first-order model (the quantified formulas registered and
asserted, and their order of relevance), the skolemization and the
instantiation manager's record, and the term database (`TermDb`: the terms of
each operator, the relevant terms, the inactive, congruent ones), with the
data of a round of checks (the term index of each operator, the relevant
domains).

The parts on the SAT context (cvc5's `context::CD*`) are undone on
backtracking, through a trail: the terms processed and their lists by
operator, the inactive and the relevant terms, the asserted quantified
formulas, and whether a conflicting instance was found. The parts on the user
context (the registered and skolemized formulas, the instantiations recorded)
and the plain ones (the order of relevance) are not.

The equality engine is seen through `Ctx`: its terms, representatives,
(dis)equalities, its classes, and cvc5's node order (`TNode`'s `<`, by node
id), which orders the term index as cvc5's `std::map`s do.
-/

namespace Telos.Solver.Quant

/-- What the quantifiers engine sees of the rest of the engine. -/
structure Ctx where
  hasTerm : Node → Bool
  rep : Node → Node
  areEqual : Node → Node → Bool
  areDisequal : Node → Node → Bool
  /-- cvc5's node order (by node id). -/
  lt : Node → Node → Bool
  /-- The representatives of the equality engine's classes, in its order
  (`EqClassesIterator`). -/
  reps : Array Node
  /-- The facts asserted to the theories (`factsBegin`), for the relevant
  terms. -/
  facts : Array Node
  rewrite : Node → Node
  /-- The terms of the class of a representative, in the equality engine's
  order (`EqClassIterator`). -/
  members : Node → Array Node := fun n => #[n]
  /-- cvc5's node order (`NodeOrder`, without the nodes made while solving),
  and the rewriter at an order (for instances, whose nodes are numbered). -/
  order : NodeOrder := {}
  rewriteAt : NodeOrder → Node → Node := fun _ n => n
  /-- The model at last call: the value of an integer term, and of a formula. -/
  modelInt : Node → Option Int := fun _ => none
  modelBool : Node → Option Bool := fun _ => none

/-- `TNodeTrie`: its children (or, at a leaf, the term), in cvc5's node order. -/
inductive Trie where
  | mk (data : Array (Node × Trie))
  deriving Inhabited

namespace Trie

def data : Trie → Array (Node × Trie)
  | .mk d => d

def empty : Trie := .mk #[]

/-- The position of `k` in `d` (sorted by `lt`), or where it goes. -/
def search (lt : Node → Node → Bool) (d : Array (Node × Trie)) (k : Node) : Nat × Bool := Id.run do
  let mut lo := 0
  let mut hi := d.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let km := d[mid]!.1
    if km == k then return (mid, true)
    if lt km k then lo := mid + 1 else hi := mid
  return (lo, false)

def find? (lt : Node → Node → Bool) (t : Trie) (k : Node) : Option Trie :=
  let (i, found) := search lt t.data k
  if found then some t.data[i]!.2 else none

/-- `addOrGetTerm`: the term indexed by `reps`, or `n`, added. -/
partial def addOrGetTerm (lt : Node → Node → Bool) (t : Trie) (n : Node) (reps : List Node) : Trie × Node :=
  match reps with
  | [] =>
    match t.data[0]? with
    | some (m, _) => (t, m)
    | none => (.mk #[(n, empty)], n)
  | r :: rs =>
    let d := t.data
    let (i, found) := search lt d r
    let child := if found then d[i]!.2 else empty
    let (child, m) := addOrGetTerm lt child n rs
    let d := if found then d.set! i (r, child) else d.insertIdx! i (r, child)
    (.mk d, m)

/-- `existsTerm`. -/
def existsTerm (lt : Node → Node → Bool) (t : Trie) (reps : List Node) : Option Node := do
  let leaf ← reps.foldlM (fun t r => t.find? lt r) t
  return (← leaf.data[0]?).1

end Trie

/-- An entry of the trail. -/
inductive Undo where
  | processed (k : Key)
  | opTerm (op : Key)
  | typeTerm (T : Option TypeNode)
  | newOp
  | inactive (k : Key)
  | hasTerm (k : Key)
  | asserted
  | conflictInst
  deriving Inhabited

/-- A pending lemma of the quantifiers' inference manager: its inference and
the lemma. -/
structure Lemma where
  id : String
  lem : Node
  /-- For its certificate: the instance `(q, t₁, …, tₙ)` and the lemma before
  its rewrite, or the formula skolemized. -/
  inst : Option (Node × Array Node × Node) := none
  skolemize : Option Node := none
  /-- The order the lemma was rewritten at. -/
  order : Option NodeOrder := none
  deriving Inhabited

structure State where
  /-- `TermDb::d_processed` (SAT context). -/
  processed : Std.HashSet Key := {}
  /-- `d_opMap`: the terms of each match operator, in order (SAT context). -/
  opTerms : Std.HashMap Key (Array Node) := {}
  /-- `d_typeMap`: the terms of each type, in order (SAT context). -/
  typeTerms : Std.HashMap (Option TypeNode) (Array Node) := {}
  /-- `d_ops` (SAT context). -/
  ops : Array Node := #[]
  /-- `d_inactive_map` (SAT context). -/
  inactive : Std.HashSet Key := {}
  /-- `d_has_map`, the relevant terms (SAT context). -/
  hasMap : Std.HashSet Key := {}
  /-- `d_par_op_map`: the operator of the applications of a parametric kind,
  by the type of their first argument (a term, the first met). -/
  parOp : Std.HashMap (Kind × Option TypeNode) Node := {}
  /-- `d_quants_prereg`, `d_quants` (user context). -/
  preregistered : Std.HashSet Key := {}
  registered : Std.HashSet Key := {}
  /-- `FirstOrderModel::d_forall_asserts` (SAT context). -/
  asserted : Array Node := #[]
  /-- `d_forall_rlv_vec`, `d_last_forall_rlv`. -/
  rlvVec : Array Node := #[]
  lastRlv : Option Node := none
  /-- `Skolemize::d_skolemized` (user context). -/
  skolemized : Std.HashSet Key := {}
  /-- The instantiations recorded, `(q, t₁, …, tₙ)` (user context). -/
  insts : Std.HashSet Key := {}
  /-- `d_conflictInst` (SAT context). -/
  conflictInst : Bool := false
  /-- The lemmas sent, by node (the inference manager's cache, user context). -/
  lemmaCache : Std.HashSet Key := {}
  /-- `d_ierCounter`, `d_ierCounterLc`, `d_ierCounterLastLc`. -/
  ierCounter : Nat := 0
  ierCounterLc : Nat := 0
  ierCounterLastLc : Nat := 0
  trail : Array Undo := #[]
  /-- The trail and list sizes saved at each push. -/
  saved : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

namespace State

/-- Record a trail entry. -/
def log (s : State) (u : Undo) : State := { s with trail := s.trail.push u }

def push (s : State) : State :=
  { s with saved := s.saved.push (s.trail.size, s.ops.size, s.asserted.size) }

/-- Undo back to the push of level `k`. -/
def popTo (s : State) (k : Nat) : State := Id.run do
  let some (tsize, osize, asize) := s.saved[k]? | return s
  let trail := s.trail
  let mut processed := s.processed
  let mut opTerms := s.opTerms
  let mut typeTerms := s.typeTerms
  let mut inactive := s.inactive
  let mut hasMap := s.hasMap
  let mut conflictInst := s.conflictInst
  let s := { s with processed := {}, opTerms := {}, typeTerms := {}, inactive := {}, hasMap := {}, trail := #[] }
  for i in [0:trail.size - tsize] do
    match trail[trail.size - 1 - i]! with
    | .processed k => processed := processed.erase k
    | .opTerm op => opTerms := opTerms.modify op Array.pop
    | .typeTerm T => typeTerms := typeTerms.modify T Array.pop
    | .newOp => pure ()
    | .inactive k => inactive := inactive.erase k
    | .hasTerm k => hasMap := hasMap.erase k
    | .asserted => pure ()
    | .conflictInst => conflictInst := false
  return { s with processed, opTerms, typeTerms, inactive, hasMap, conflictInst, trail := trail.take tsize,
                  ops := s.ops.take osize, asserted := s.asserted.take asize, saved := s.saved.take k }

end State

/-- The data of a round of checks (`TermDb::reset`): the term index of each
operator (`d_func_map_trie`), by class (`d_func_map_eqc_trie`), the
representatives of the arguments of each term (`d_arg_reps`), the relevant
domains (`d_fmapRelDom`), and the lemmas pending. -/
structure Round where
  funTrie : Std.HashMap Key Trie := {}
  ufTermsDone : Std.HashSet Key := {}
  eqcTrie : Std.HashMap Key Trie := {}
  argReps : Std.HashMap Key (Array Node) := {}
  relDom : Std.HashMap Key (Array (Array Node)) := {}
  pending : Array Lemma := #[]
  /-- The term database found disequal congruent terms (`notifyInConflict`). -/
  inConflict : Bool := false
  deriving Inhabited

structure S where
  st : State
  rd : Round := {}
  deriving Inhabited

abbrev M := ReaderT Ctx (StateM S)

def getSt : M State := return (← get).st
def modifySt (f : State → State) : M Unit :=
  modify fun s =>
    let st := s.st
    let s := { s with st := default }
    { s with st := f st }
def modifyRd (f : Round → Round) : M Unit :=
  modify fun s =>
    let rd := s.rd
    let s := { s with rd := default }
    { s with rd := f rd }

/-! ## Nodes -/

/-- `TriggerTermInfo::isAtomicTriggerKind`. -/
def isAtomicTriggerKind (k : Kind) : Bool :=
  k == .APPLY_UF || k == .SELECT || k == .STORE || k == .APPLY_CONSTRUCTOR ||
    k == .APPLY_SELECTOR || k == .APPLY_TESTER || k == .SET_UNION || k == .SET_INTER ||
    k == .SET_SUBSET || k == .SET_MINUS || k == .SET_MEMBER || k == .SET_SINGLETON ||
    k == .STRING_LENGTH

/-- The kinds whose match operator is a term of the kind, by the type of the
first argument (`getMatchOperator`'s parametric kinds). -/
def isParametricMatchKind (k : Kind) : Bool :=
  k == .SELECT || k == .STORE || k == .SET_UNION || k == .SET_INTER || k == .SET_SUBSET ||
    k == .SET_MINUS || k == .SET_MEMBER || k == .SET_SINGLETON || k == .APPLY_SELECTOR ||
    k == .APPLY_TESTER || k == .STRING_LENGTH

/-- `TermUtil::isBoolConnectiveTerm` (no separation logic). -/
def isBoolConnectiveTerm (n : Node) : Bool :=
  match n.getKind, n.getChildren with
  | .OR, _ | .AND, _ | .FORALL, _ | .NOT, _ => true
  | .EQUAL, #[a, _] => a.typeHint == some .boolean
  | .ITE, _ => n.typeHint == some .boolean
  | _, _ => false

/-- Whether `n` has a bound variable, free in it (`expr::hasBoundVar` for the
bound variables of a quantifier's body). Memoized. -/
partial def hasBoundVar (n : Node) : Bool :=
  let rec go (m : Std.HashMap Key Bool) (n : Node) : Std.HashMap Key Bool × Bool :=
    match m.get? ⟨n⟩ with
    | some b => (m, b)
    | none =>
      let (m, b) := match n with
        | .boundVar .. => (m, true)
        | .app _ cs => cs.foldl (fun (m, b) c => if b then (m, b) else go m c) (m, false)
        | .skolem _ cs => cs.foldl (fun (m, b) c => if b then (m, b) else go m c) (m, false)
        | _ => (m, false)
      (m.insert ⟨n⟩ b, b)
  (go {} n).2

/-- The variables of a quantified formula `(forall (x₁ … xₙ) body)`. -/
def quantVars (q : Node) : Array Node :=
  match q.getChildren[0]? with
  | some (Node.app (.kind .BOUND_VAR_LIST) vs) => vs
  | _ => #[]

def quantBody (q : Node) : Node := q.getChildren[1]!

/-- `n` with the variables `vs` replaced by `ts`, simultaneously, but under
the binders of their variables (`Node::substitute`). Memoized: linear in the
number of distinct subterms. -/
partial def substitute (vs ts : Array Node) (n : Node) : Node :=
  let σ : Std.HashMap Key Node := (vs.zip ts).foldl (fun m (v, t) => m.insert ⟨v⟩ t) {}
  let rec go (m : Std.HashMap Key Node) (n : Node) : Std.HashMap Key Node × Node :=
    match m.get? ⟨n⟩ with
    | some r => (m, r)
    | none =>
      let (m, r) := match n with
        | .boundVar .. => (m, (σ.get? ⟨n⟩).getD n)
        | .app op cs =>
          -- a binder of one of the variables shadows it: left as it is
          let shadows := (n.getKind == Kind.FORALL || n.getKind == Kind.EXISTS) &&
            (quantVars n).any fun v => σ.contains ⟨v⟩
          if shadows then (m, n) else
          let (m, ds) := cs.foldl (fun (acc : Std.HashMap Key Node × Array Node) c =>
            let (m, d) := go acc.1 c; (m, acc.2.push d)) (m, #[])
          (m, if ds == cs then n else .app op ds)
        | _ => (m, n)
      (m.insert ⟨n⟩ r, r)
  (go {} n).2

/-! ## The term database (`TermDb`) -/

/-- `getMatchOperator`: the operator of an atomic trigger term (the function of
an application, the constructor; for a parametric kind, the first term met
with the kind and the type of its first argument), if it is one. -/
def getMatchOperator (n : Node) : M (Option Node) := do
  let k := n.getKind
  if isParametricMatchKind k then
    let key := (k, n.getChildren[0]?.bind (·.typeHint))
    match (← getSt).parOp.get? key with
    | some m => return some m
    | none =>
      modifySt fun s => { s with parOp := s.parOp.insert key n }
      return some n
  if isAtomicTriggerKind k then
    match n with
    | .app (.node _ f) _ => return some f
    | _ => return none
  return none

/-- `TermDb::addTerm`: the term and its subterms (not under binders), to the
lists of their match operators. -/
partial def addTerm (n : Node) : M Unit := do
  if (← getSt).processed.contains ⟨n⟩ then return
  modifySt fun s => (s.log (.processed ⟨n⟩)) |> fun s => { s with processed := s.processed.insert ⟨n⟩ }
  modifySt fun s => { (s.log (.typeTerm n.typeHint)) with
    typeTerms := s.typeTerms.alter n.typeHint fun l => some ((l.getD #[]).push n) }
  if let some op ← getMatchOperator n then
    modifySt fun s =>
      let fresh := !s.opTerms.contains ⟨op⟩
      let s := if fresh then { (s.log .newOp) with ops := s.ops.push op } else s
      let s := s.log (.opTerm ⟨op⟩)
      { s with opTerms := s.opTerms.alter ⟨op⟩ fun l => some ((l.getD #[]).push n) }
  if n.getKind != .FORALL && n.getKind != .EXISTS then
    for c in n.getChildren do addTerm c

/-- `TermRegistry::getTermForType`: for a closed enumerable type, its first
enumerated term (`false`, `0`); else the first term of the type
(`getOrMakeTypeGroundTerm`); none if there is none (cvc5 makes a fresh
`@ground_term` skolem, not ported). -/
def getTermForType (T : Option TypeNode) : M (Option Node) := do
  match T with
  | some .boolean => return some Node.mkFalse
  | some .integer => return some (.const (.integer 0))
  | some .real => return some (.const (.rational 0))
  | _ => return ((← getSt).typeTerms.get? T).bind (·[0]?)

/-- `setHasTerm`: the term and its subterms are relevant. -/
partial def setHasTerm (n : Node) : M Unit := do
  if (← getSt).hasMap.contains ⟨n⟩ then return
  modifySt fun s => { (s.log (.hasTerm ⟨n⟩)) with hasMap := s.hasMap.insert ⟨n⟩ }
  for c in n.getChildren do setHasTerm c

/-- `hasTermCurrent` (`term-db-mode=relevant-all-delay`). -/
def hasTermCurrent (n : Node) : M Bool := return (← getSt).hasMap.contains ⟨n⟩

def isTermActive (n : Node) : M Bool := return !(← getSt).inactive.contains ⟨n⟩

def setTermInactive (n : Node) : M Unit :=
  modifySt fun s => if s.inactive.contains ⟨n⟩ then s else
    { (s.log (.inactive ⟨n⟩)) with inactive := s.inactive.insert ⟨n⟩ }

/-- `TermDb::reset` at full effort and last call: the round's data cleared, and
the terms of the facts relevant. -/
def resetTermDb : M Unit := do
  modifyRd fun r => { r with funTrie := {}, ufTermsDone := {}, eqcTrie := {}, argReps := {}, relDom := {} }
  for f in (← read).facts do setHasTerm f

/-- `computeArgReps`. -/
def argReps (n : Node) : M (Array Node) := do
  if let some r := (← get).rd.argReps.get? ⟨n⟩ then return r
  let c ← read
  let r := n.getChildren.map fun a => if c.hasTerm a then c.rep a else a
  modifyRd fun rd => { rd with argReps := rd.argReps.insert ⟨n⟩ r }
  return r

/-- `computeUfTerms`: the term index of `f`, its congruent terms inactive, and
its relevant domains; two disequal congruent terms are a lemma
(`QUANTIFIERS_TDB_DEQ_CONG`) and a conflict. -/
def computeUfTerms (f : Node) : M Unit := do
  if (← get).rd.ufTermsDone.contains ⟨f⟩ then return
  modifyRd fun rd => { rd with ufTermsDone := rd.ufTermsDone.insert ⟨f⟩ }
  let c ← read
  let terms := ((← getSt).opTerms.get? ⟨f⟩).getD #[]
  for n in terms do
    if !(← hasTermCurrent n) || !c.hasTerm n then continue
    if !(← isTermActive n) then continue
    let reps ← argReps n
    let trie := ((← get).rd.funTrie.get? ⟨f⟩).getD .empty
    let (trie, a0) := trie.addOrGetTerm c.lt n reps.toList
    modifyRd fun rd => { rd with funTrie := rd.funTrie.insert ⟨f⟩ trie }
    if a0 != n && c.areEqual a0 n then
      setTermInactive n
      continue
    if c.areDisequal a0 n then
      let antec := ((a0.getChildren.zip n.getChildren).filter fun (a, b) => a != b).map
        fun (a, b) => Node.eqNode a b
      let ante := if antec.size == 1 then antec[0]! else if antec.isEmpty then Node.mkTrue
        else Node.mkNode .AND antec
      let lem := Node.mkNode .IMPLIES #[ante, Node.eqNode a0 n]
      modifyRd fun rd => { rd with pending := rd.pending.push { id := "QUANTIFIERS_TDB_DEQ_CONG", lem },
                                   inConflict := true }
      return
    modifyRd fun rd =>
      let frds := (rd.relDom.get? ⟨f⟩).getD #[]
      let frds := if frds.size < reps.size then frds ++ Array.replicate (reps.size - frds.size) #[] else frds
      let frds := (List.range reps.size).foldl (fun frds i =>
        let r := reps[i]!
        if frds[i]!.contains r then frds else frds.modify i (·.push r)) frds
      { rd with relDom := rd.relDom.insert ⟨f⟩ frds }

/-- `computeUfEqcTerms`: the index of the terms of `f` by their class, then
the representatives of their arguments. -/
def computeUfEqcTerms (f : Node) : M Trie := do
  if let some t := (← get).rd.eqcTrie.get? ⟨f⟩ then return t
  let c ← read
  let mut trie : Trie := .empty
  for n in ((← getSt).opTerms.get? ⟨f⟩).getD #[] do
    if (← hasTermCurrent n) && (← isTermActive n) then
      let reps ← argReps n
      let r := if c.hasTerm n then c.rep n else n
      trie := (trie.addOrGetTerm c.lt n (r :: reps.toList)).1
  modifyRd fun rd => { rd with eqcTrie := rd.eqcTrie.insert ⟨f⟩ trie }
  return trie

/-- `inRelevantDomain`. -/
def inRelevantDomain (f : Node) (i : Nat) (r : Node) : M Bool := do
  computeUfTerms f
  match (← get).rd.relDom.get? ⟨f⟩ with
  | some rd => return (rd[i]?.map (·.contains r)).getD false
  | none => return false

/-- `getCongruentTerm` for the representatives `args`. -/
def getCongruentTerm (f : Node) (args : Array Node) : M (Option Node) := do
  computeUfTerms f
  match (← get).rd.funTrie.get? ⟨f⟩ with
  | some t => return t.existsTerm (← read).lt args.toList
  | none => return none

/-! ## Entailment checks (`EntailmentCheck`) -/

/-- A substitution of bound variables, and whether its terms are
representatives (`subsRep`). -/
abbrev Subs := Std.HashMap Key Node

mutual
  /-- `getEntailedTerm2`. -/
  partial def getEntailedTerm (n : Node) (subs : Subs) (subsRep : Bool) : M (Option Node) := do
    let c ← read
    if c.hasTerm n then return some n
    match n with
    | .boundVar .. =>
      match subs.get? ⟨n⟩ with
      | some t => if subsRep then return some t else getEntailedTerm t subs subsRep
      | none => return none
    | _ =>
      if n.getKind == .ITE then
        let cs := n.getChildren
        for i in [0, 1] do
          if ← isEntailed cs[0]! subs subsRep (i == 0) then
            return ← getEntailedTerm cs[if i == 0 then 1 else 2]! subs subsRep
        return none
      if let some f ← getMatchOperator n then
        let mut args := #[]
        for a in n.getChildren do
          let some t ← getEntailedTerm a subs subsRep | return none
          args := args.push (c.rep t)
        return ← getCongruentTerm f args
      return none

  /-- `isEntailed2`. -/
  partial def isEntailed (n : Node) (subs : Subs) (subsRep : Bool) (pol : Bool) : M Bool := do
    let c ← read
    let cs := n.getChildren
    match n.getKind with
    | .EQUAL =>
      if cs[0]!.typeHint != some .boolean then
        let n1 ← if cs[0]!.isConst then pure (some cs[0]!) else getEntailedTerm cs[0]! subs subsRep
        let some n1 := n1 | return false
        let n2 ← if cs[1]!.isConst then pure (some cs[1]!) else getEntailedTerm cs[1]! subs subsRep
        let some n2 := n2 | return false
        return if pol then c.areEqual n1 n2 else c.areDisequal n1 n2
      for i in [0, 1] do
        if ← isEntailed cs[0]! subs subsRep (i == 0) then
          return ← isEntailed cs[1]! subs subsRep (if i == 0 then pol else !pol)
      return false
    | .NOT => isEntailed cs[0]! subs subsRep !pol
    | .OR | .AND =>
      let simPol := (pol && n.getKind == .OR) || (!pol && n.getKind == .AND)
      for d in cs do
        if ← isEntailed d subs subsRep pol then
          if simPol then return true
        else if !simPol then return false
      return !simPol
    | .ITE =>
      for i in [0, 1] do
        if ← isEntailed cs[0]! subs subsRep (i == 0) then
          return ← isEntailed cs[if i == 0 then 1 else 2]! subs subsRep pol
      return false
    | .FORALL => if !pol then isEntailed cs[1]! subs subsRep pol else return false
    | .APPLY_UF =>
      match ← getEntailedTerm n subs subsRep with
      | some t =>
        let r := c.rep t
        return r.isConst && r == Node.mkBool pol
      | none => return false
    | _ =>
      match n with
      | .boundVar .. =>
        match ← getEntailedTerm n subs subsRep with
        | some t =>
          let r := c.rep t
          return r.isConst && r == Node.mkBool pol
        | none => return false
      | _ => return false
end

/-- `evaluateTerm2` (`useEntailmentTests` off): the value of `n` under the
substitution, modulo the equality engine; `none` if a subterm has none (with
`reqHasTerm`, a term the engine does not have). -/
partial def evaluateTerm (n : Node) (subs : Subs) (subsRep : Bool) (reqHasTerm : Bool) : M (Option Node) := do
  let visited ← modifyGet fun s => ((), s)
  let _ := visited
  let rec go (n : Node) (reqHasTerm : Bool) : StateT (Std.HashMap Key (Option Node)) M (Option Node) := do
    if let some r := (← get).get? ⟨n⟩ then return r
    let c ← read
    let mut ret : Option Node := some n
    let mut req := reqHasTerm
    let k := n.getKind
    if k == .FORALL then pure ()
    else if let .boundVar .. := n then
      if let some t := subs.get? ⟨n⟩ then ret := some (if subsRep then t else c.rep t)
    else if c.hasTerm n then
      ret := some (c.rep n)
      req := false
    else if let .app op cs := n then
      let mut args : Array Node := #[]
      let mut set := false
      for i in [0:cs.size] do
        let some a ← go cs[i]! req | ret := none; set := true; break
        if a == Node.mkTrue || a == Node.mkFalse then
          if (k == .AND && a == Node.mkFalse) || (k == .OR && a == Node.mkTrue) then
            ret := some a; set := true; req := false; break
          if k == .ITE && i == 0 then
            ret ← go cs[if a == Node.mkTrue then 1 else 2]! req
            set := true; req := false; break
        args := args.push a
      if !set then
        let f ← (getMatchOperator n : M _)
        let mut found := false
        if let some f := f then
          if let some nn ← (getCongruentTerm f args : M _) then
            ret := some (c.rep nn); found := true; req := false
        if !found then
          let r := c.rewrite (.app op args)
          ret := some (match r with
            | .app (.kind .EQUAL) #[a, b] => if c.areDisequal a b then Node.mkFalse else r
            | _ => r)
    if req then
      if let some r := ret then
        let rk := r.getKind
        if rk != .OR && rk != .AND && rk != .EQUAL && rk != .ITE && rk != .NOT && rk != .FORALL then
          if !c.hasTerm r then ret := none
    modify fun m => m.insert ⟨n⟩ ret
    return ret
  (go n reqHasTerm).run' {}

end Telos.Solver.Quant
