import Std.Data.HashMap
import Telos.Solver.EqualityEngine
import Telos.Solver.EqProof
import Telos.Solver.Theory.DtType
import Telos.Solver.StringsCore

/-!
# Equality proofs from the equality engine

The certificate (`EqProof`, `Telos/Solver/EqProof.lean`) of an equality that
the equality engine derived: a path in its equality graph, each edge justified
by its reason.
- An edge asserted with a reason is that assumption, possibly flipped (`symm`).
- A congruence edge between two applications is `cong` of the arguments'
  proofs. The engine curries applications: `f(a₁, …, aₙ)` is the application of
  the node of `f(a₁, …, aₙ₋₁)` to `aₙ`, and those internal nodes are merged by
  congruence too. So the proof of the `i`-th arguments follows the path between
  the internal nodes, position by position (`congArgs`).
- A reflexivity edge, of `(= a b)` with `true` once `a` and `b` are merged, is
  `eqTrue` of the proof of `(a, b)`.
- Edges between constants evaluated from interpreted applications are not
  supported (no theory uses them yet): the builder fails.
- An edge asserted by a theory, an internal fact, is proven by its inference
  (`proveFact`), from the proofs of its premises in the engine and, for its
  theory reasoning, CPC rule instances that Logos's checker accepts
  (`EqProof.valid`).

The builder is not trusted: the checker checks what it builds, and the
engine answers `unsat` only if the check succeeds.
-/

namespace Telos.Solver.EE

open Telos.Solver

/-- What the builder knows: the engine, the index of each assumption, all the
asserted literals, and, for each of their subterms, a literal it occurs in. -/
structure BuildCtx where
  ee : EqualityEngine
  index : Std.HashMap Key Nat
  lits : Array Node
  owner : Std.HashMap Key Nat

/-- The assumptions so far, and a path to each of their subterms. A congruence
may relate a term that occurs in none of the explanation's literals, only in
another asserted literal: that literal is then added to the assumptions. -/
structure BuildState where
  A : Array Node
  paths : Std.HashMap Key SubPath

abbrev BuildM := StateT BuildState (Except String)

/-- Paths to the subterms of the assumptions, below operators whose children
are well typed when they are (`EqProof.follow`): a traversal of each
assumption as a DAG, the first path found to each subterm. -/
def subtermPaths (A : Array Node) (m : Std.HashMap Key SubPath := {}) (start : Nat := 0) :
    Std.HashMap Key SubPath := Id.run do
  let mut m := m
  for h : i in [start:A.size] do
    -- (node, reversed path)
    let mut stack : Array (Node × List Nat) := #[(A[i], [])]
    while h' : stack.size > 0 do
      let (t, rp) := stack[stack.size - 1]
      stack := stack.pop
      if m.contains ⟨t⟩ then continue
      m := m.insert ⟨t⟩ { root := i, path := rp.reverse }
      if let .app op cs := t then
        if op.childrenTypedOfParent then
          for j in [0:cs.size] do
            stack := stack.push (cs[j]!, j :: rp)
  return m

/-- The edges of a path from `t₁` to `t₂` in the equality graph, in order, as
(source, target, edge), by the breadth-first search of `getExplanation`. -/
def findPath (ee : EqualityEngine) (t₁ t₂ : Nat) : Option (Array (Nat × Nat × Edge)) := Id.run do
  let mut queue : Array (Nat × Option Nat × Nat) := #[(t₁, none, 0)]
  let mut idx := 0
  while idx < queue.size do
    let (cur, curEdge, _) := queue[idx]!
    let mut e := ee.graph[cur]!
    while h : e.isSome do
      let eid := e.get h
      let edge := ee.edges[eid]!
      let backward := match curEdge with
        | some ce => (eid ||| 1) == (ce ||| 1)
        | none => false
      if !backward then
        if edge.node == t₂ then
          let mut out : Array (Nat × Nat × Edge) := #[(cur, t₂, edge)]
          let mut ci := idx
          let mut fuel := queue.size
          while fuel > 0 do
            fuel := fuel - 1
            let (n, reach, prev) := queue[ci]!
            match reach with
            | some r =>
              out := out.push ((queue[prev]!).1, n, ee.edges[r]!)
              ci := prev
            | none => break
          return some out.reverse
        queue := queue.push (edge.node, some eid, idx)
      e := edge.next
    idx := idx + 1
  return none

/-- Compose two argument proofs: `none` is the identity. -/
def composeArg : Option EqProof → Option EqProof → Option EqProof
  | none, q => q
  | p, none => p
  | some p, some q => some (.trans p q)

/-- The literals of `lits` that each subterm occurs in, the first. -/
def subtermOwners (lits : Array Node) : Std.HashMap Key Nat :=
  (subtermPaths lits).fold (fun m k p => m.insert k p.root) {}

/-- A path to `t` from the assumptions, adding the asserted literal it occurs
in if needed. -/
def pathTo (C : BuildCtx) (t : Node) : BuildM SubPath := do
  if let some p := (← get).paths.get? ⟨t⟩ then return p
  let some j := C.owner.get? ⟨t⟩ | throw "a congruence term is in no asserted literal"
  let lit := C.lits[j]!
  modify fun st =>
    let A := st.A.push lit
    { A, paths := subtermPaths A st.paths (A.size - 1) }
  let some p := (← get).paths.get? ⟨t⟩ | throw "a congruence term is not below its literal"
  return p

mutual
  /-- A proof of `(nodes[t₁], nodes[t₂])`, or `none` if they are the same node;
  fails if the builder cannot justify an edge. -/
  partial def proveIds (C : BuildCtx) (t₁ t₂ : Nat) : BuildM (Option EqProof) := do
    if t₁ == t₂ then return none
    let some path := findPath C.ee t₁ t₂ | throw "no path in the equality graph"
    let mut acc : Option EqProof := none
    for (cur, next, edge) in path do
      let p ← proveEdge C cur next edge
      acc := composeArg acc (some p)
    return acc

  /-- A proof of `(nodes[cur], nodes[next])` for one edge. -/
  partial def proveEdge (C : BuildCtx) (cur next : Nat) (edge : Edge) : BuildM EqProof := do
    let ee := C.ee
    let a := ee.nodes[cur]!
    let b := ee.nodes[next]!
    match edge.type with
    | .equality =>
      let asAssumption : Option EqProof := match C.index.get? ⟨edge.reason⟩ with
        | some i =>
          let (x, y) := EqProof.assumptionEq edge.reason
          if x == a && y == b then some (.assume i)
          else if x == b && y == a then some (.symm (.assume i))
          else none
        | none => none
      match asAssumption with
      | some p => return p
      | none =>
        -- an internal fact of a theory (whose explanation may be an assumption)
        let cands := [Node.eqNode a b, Node.eqNode b a] ++
          (if b == Node.mkTrue then [a] else []) ++ (if a == Node.mkTrue then [b] else [])
        for conc in cands do
          if let some (id, exp) := ee.dt.facts.get? ⟨conc⟩ <|> ee.sets.facts.get? ⟨conc⟩ <|>
              ee.strings.facts.get? ⟨conc⟩ then
            let p ← proveFact C conc id exp
            let (x, y) := EqProof.assumptionEq conc
            if x == a && y == b then return p
            if x == b && y == a then return .symm p
        throw "a reason is not an assumption"
    | .congruence =>
      let args ← appArgs C cur next
      -- a term no asserted literal has (a theory's): its typing is checked
      match ← (try (some <$> pathTo C a) catch _ => pure none) with
      | some src => return .cong src args
      | none => return .congAt a args
    | .reflexivity =>
      let eqId := if cur == ee.trueId then next else cur
      let some (f, _) := ee.apps[eqId]! | throw "a reflexivity edge without an equality"
      let some p ← proveIds C f.a f.b | throw "a reflexivity of identical terms"
      let q := EqProof.eqTrue p
      return if cur == ee.trueId then .symm q else q
    | .constants =>
      -- an application whose arguments are equal to constants is its value: by
      -- congruence, then the rewriter
      let (t, v, tFirst) := if a.isConst then (b, a, false) else (a, b, true)
      let evaluated : BuildM (Option EqProof) := do
        let .app _ cs := t | return none
        if !v.isConst then return none
        let mut args : Array (Option EqProof) := #[]
        let mut ds : Array Node := #[]
        for c in cs do
          let some i := ee.nodeIds.get? ⟨c⟩ | return none
          let r := find ee i
          let rc := ee.nodes[r]!
          if !rc.isConst then return none
          args := args.push (← proveIds C i r)
          ds := ds.push rc
        let .app op _ := t | return none
        let t' := Node.app op ds
        if Telos.rewrite t' != v then return none
        let p : EqProof := if args.all (·.isNone) then .rw t else .trans (.congAt t args) (.rw t')
        return some (if tFirst then p else .symm p)
      if let some p ← evaluated then return p
      -- an equality whose sides are equal to distinct constructor constants is
      -- false (`dt-cons-eq-clash`)
      let (e, eFirst) := if b == Node.mkFalse then (a, true) else (b, false)
      let .app (.kind .EQUAL) #[x, y] := e | throw "merges of evaluated constants are not supported"
      let some ix := ee.nodeIds.get? ⟨x⟩ | throw "a term is not in the engine"
      let some iy := ee.nodeIds.get? ⟨y⟩ | throw "a term is not in the engine"
      let cx := ee.nodes[find ee ix]!
      let cy := ee.nodes[find ee iy]!
      -- distinct values (strings, numbers): the rewriter evaluates the
      -- equality to `false`
      let values := cx.isConst && cy.isConst && Telos.rewrite (Node.eqNode cx cy) == Node.mkFalse
      if !values && ((DT.consApp? cx).isNone || (DT.consApp? cy).isNone) then
        throw "merges of evaluated constants are not supported"
      let px ← proveIds C ix (find ee ix)
      let py ← proveIds C iy (find ee iy)
      let lem := Node.eqNode (Node.eqNode cx cy) Node.mkFalse
      let v := if values then EqProof.rw (Node.eqNode cx cy)
        else EqProof.valid lem [DT.ruleStep .dt_cons_eq_clash lem]
      let p := if px.isNone && py.isNone then v else .trans (.congAt e #[px, py]) v
      return if eFirst then p else .symm p

  /-- The argument proofs of two applications merged by one congruence edge. -/
  partial def appArgs (C : BuildCtx) (cur next : Nat) : BuildM (Array (Option EqProof)) := do
    let ee := C.ee
    let some (f₁, _) := ee.apps[cur]! | throw "a congruence edge without an application"
    let some (f₂, _) := ee.apps[next]! | throw "a congruence edge without an application"
    let last ← proveIds C f₁.b f₂.b
    match f₁.type with
    | .equality =>
      let first ← proveIds C f₁.a f₂.a
      return #[first, last]
    | _ =>
      let k := (children ee.nodes[cur]!).size
      let prefixArgs ← congArgs C f₁.a f₂.a (k - 1)
      return prefixArgs.push last

  /-- The argument proofs of two internal application nodes with `k` arguments
  that the engine merged, along the path between them. -/
  partial def congArgs (C : BuildCtx) (x y : Nat) (k : Nat) : BuildM (Array (Option EqProof)) := do
    if x == y then return Array.replicate k none
    if k == 0 then throw "different operators merged"
    let some path := findPath C.ee x y | throw "no path between applications"
    let mut acc : Array (Option EqProof) := Array.replicate k none
    for (cur, next, edge) in path do
      if edge.type != .congruence then throw "internal nodes merged other than by congruence"
      let some (f₁, _) := C.ee.apps[cur]! | throw "no application"
      let some (f₂, _) := C.ee.apps[next]! | throw "no application"
      let last ← proveIds C f₁.b f₂.b
      let pre ← congArgs C f₁.a f₂.a (k - 1)
      let step := pre.push last
      acc := (acc.zip step).map fun (p, q) => composeArg p q
    return acc

  /-- A proof of `(t₁, t₂)` for terms of the engine. -/
  partial def proveT (C : BuildCtx) (t₁ t₂ : Node) : BuildM (Option EqProof) := do
    let some i₁ := C.ee.nodeIds.get? ⟨t₁⟩ | throw "a term is not in the engine"
    let some i₂ := C.ee.nodeIds.get? ⟨t₂⟩ | throw "a term is not in the engine"
    proveIds C i₁ i₂

  /-- A proof of what the internal fact `conc` gives as an assumption, from its
  inference `id` and explanation `exp` (the datatypes theory's). -/
  partial def proveFact (C : BuildCtx) (conc : Node) (id : String) (exp : Node) : BuildM EqProof := do
    match id with
    | "DATATYPES_UNIF" =>
      -- `(= c₁ c₂)` and `dt-cons-eq` give the equalities of the arguments
      let .app (.kind .EQUAL) #[c₁, c₂] := exp | throw "a unification without an equality"
      let some (_, _, as) := DT.consApp? c₁ | throw "a unification of a non-constructor"
      let some (_, _, bs) := DT.consApp? c₂ | throw "a unification of a non-constructor"
      let eqs := (as.zip bs).map fun (a, b) => Node.eqNode a b
      let B := if eqs.size == 1 then eqs[0]! else .app (.kind .AND) eqs
      let lem := Node.eqNode exp B
      let v := EqProof.valid lem [DT.ruleStep .dt_cons_eq lem]
      let some p ← proveT C c₁ c₂ | throw "a unification of identical terms"
      let q := EqProof.trans (.symm v) (.eqTrue p)
      if eqs.size == 1 then return .fromTrue q
      let some k := eqs.findIdx? (· == conc) | throw "a unification without its equality"
      return .fromTrue (.andElim k q)
    | "DATATYPES_COLLAPSE_SEL" =>
      -- the selector of a term equal to a constructor term is its argument
      let .app (.kind .EQUAL) #[s, r] := conc | throw "a collapse without an equality"
      let some (T, i, j, s₀) := DT.selApp? s | throw "a collapse of a non-selector"
      let .app (.kind .EQUAL) #[_, c] := exp | throw "a collapse without its explanation"
      let some (_, _, cs) := DT.consApp? c | throw "a collapse without a constructor"
      if cs[j]? != some r then throw "a collapse to another term"
      let selc := DT.mkSel T i j c
      let lem := Node.eqNode selc r
      let v := EqProof.valid lem [DT.ruleStep .dt_collapse_selector lem]
      match ← proveT C s₀ c with
      | some p => return .trans (.congAt s #[some p]) v
      | none => return v
    | "DATATYPES_INST" =>
      -- a tester and `dt-inst`
      if exp == Node.mkTrue then throw "an instantiation of a constructor term is not supported"
      let lem := Node.eqNode exp conc
      let v := EqProof.valid lem [DT.ruleStep .dt_inst lem]
      let some p ← proveT C exp Node.mkTrue | throw "a tester that is true"
      return .fromTrue (.trans (.symm v) p)
    | "DATATYPES_SPLIT" =>
      -- the tester of the only constructor
      let lem := Node.eqNode conc Node.mkTrue
      return .valid lem [DT.ruleStep .dt_collapse_tester_singleton lem]
    | "DATATYPES_LABEL_EXH" =>
      -- the split of the term, and the other testers false
      let some (k, targ) := DT.isTester? conc | throw "an exhaustion without a tester"
      let some T := DT.dtType? targ | throw "an exhaustion of a non-datatype"
      let parts := match exp with
        | .app (.kind .AND) ps => ps
        | e => #[e]
      let split := DT.mkSplit targ T
      let .app (.kind .OR) ls := split | throw "an exhaustion of one constructor"
      let v := EqProof.valid split [DT.argStep .dt_split targ]
      let mut qs : Array EqProof := #[]
      for i in [0:ls.size] do
        if i == k then continue
        -- the label `(not (is-Cᵢ x))`, with `x` equal to `targ`
        let lab? := parts.find? fun l => match l with
          | .app (.kind .NOT) #[a] => (DT.isTester? a).map (·.1) == some i
          | _ => false
        let some (.app (.kind .NOT) #[a]) := lab? | throw "an exhaustion without a label"
        let some (_, x) := DT.isTester? a | throw "a label without a tester"
        let some pa ← proveT C a Node.mkFalse | throw "a label that is false"
        match ← proveT C x targ with
        | some e => qs := qs.push (.trans (.symm (.congAt a #[some e])) pa)
        | none => qs := qs.push pa
      return .orElim k v qs.toList
    | "SETS_SINGLETON_EQ" =>
      -- `{x} = {y}`: `x` is in `{x}`, so in `{y}`, which is `(= x y)`
      let .app (.kind .EQUAL) #[s₁@(.app (.kind .SET_SINGLETON) #[x]), s₂] := exp
        | throw "a singleton equality without singletons"
      let some p ← proveT C s₁ s₂ | throw "a singleton equality of identical terms"
      let m₁ := Node.mkNode .SET_MEMBER #[x, s₁]
      let m₂ := Node.mkNode .SET_MEMBER #[x, s₂]
      if Telos.rewrite m₁ != Node.mkTrue || Telos.rewrite conc != Telos.rewrite m₂ then
        throw "a singleton equality the rewriter does not decide"
      let t : EqProof := .trans (.rw conc) (.trans (.symm (.rw m₂)) (.trans (.symm (.congAt m₁ #[none, some p])) (.rw m₁)))
      return .fromTrue t
    | "SETS_MEM_EQ" | "SETS_EQ_MEM" =>
      -- `(set.member x s)` with `s` equal to `{e}`: `(set.member x {e})`, which is
      -- `(= x e)`
      let parts := match exp with
        | .app (.kind .AND) ps => ps
        | e => #[e]
      let some atom := parts.find? fun l => match l with | .app (.kind .SET_MEMBER) _ => true | _ => false
        | throw "a membership fact without its membership"
      let .app (.kind .SET_MEMBER) #[x, s] := atom | throw "a membership fact without its membership"
      let some (.app (.kind .EQUAL) #[_, sg]) := parts.find? fun l => match l with
          | .app (.kind .EQUAL) _ => true
          | _ => false
        | throw "a membership fact without its singleton"
      let some pa ← proveT C atom Node.mkTrue | throw "a membership that is true"
      let m' := Node.mkNode .SET_MEMBER #[x, sg]
      if Telos.rewrite conc != Telos.rewrite m' then throw "a membership fact the rewriter does not decide"
      let q : EqProof := match ← proveT C s sg with
        | some ps => .trans (.symm (.congAt atom #[none, some ps])) pa
        | none => pa
      return .fromTrue (.trans (.rw conc) (.trans (.symm (.rw m')) q))
    | _ =>
      if id.startsWith "STRINGS_" then
        -- a core inference of strings: its premises from the engine, and its
        -- CPC proof (`Telos/Solver/StringsCore.lean`)
        let P := match exp with
          | .app (.kind .AND) ps => ps
          | e => if e == Node.mkTrue then #[] else #[e]
        let ps ← P.mapM (proveLitTrue C)
        let some q := StringsCore.proveFrom id P ps conc | throw s!"an internal fact of {id} without a proof"
        return .fromTrue q
      throw s!"an internal fact of {id} is not supported"

  /-- A proof of `(l, true)` for a literal `l` that the engine entails. -/
  partial def proveLitTrue (C : BuildCtx) (l : Node) : BuildM EqProof := do
    -- `((not x), true)` from `(x, false)`
    let notTrue (x : Node) (p : EqProof) : EqProof :=
      .trans (.congAt (Node.notNode x) #[some p]) (.rw (Node.notNode Node.mkFalse))
    match l with
    | .app (.kind .NOT) #[e@(.app (.kind .EQUAL) #[a, b])] =>
      let p ← try proveDiseq C a b catch _ => do
        let some p ← proveT C e Node.mkFalse | throw "a disequality that is false"
        pure p
      return notTrue e p
    | .app (.kind .EQUAL) #[a, b] =>
      match ← proveT C a b with
      | some p => return .eqTrue p
      | none => return .rw (Node.eqNode a a)
    | .app (.kind .NOT) #[x] =>
      let some p ← proveT C x Node.mkFalse | throw "a literal that is false"
      return notTrue x p
    | x =>
      let some p ← proveT C x Node.mkTrue | throw "a literal that is true"
      return p

  /-- A proof of `((= a b), false)`, from the reasons of the propagated
  disequality of `a` and `b`. Only a disequality propagated by a trigger (whose
  reason is the merge of the equality with `false`) is supported, in either
  orientation (by `rw`, the two having the same rewrite). -/
  partial def proveDiseq (C : BuildCtx) (a b : Node) : BuildM EqProof := do
    let some i := C.ee.nodeIds.get? ⟨a⟩ | throw "a term is not in the engine"
    let some j := C.ee.nodeIds.get? ⟨b⟩ | throw "a term is not in the engine"
    let some (lo, hi) := C.ee.diseqReasons.get? (i, j) | throw "no reasons for a disequality"
    if hi != lo + 1 then throw "a disequality from several reasons is not supported"
    let (x, y) := C.ee.deducedReasons[lo]!
    if y != C.ee.falseId then throw "a disequality reason is not a merge with false"
    let some p ← proveIds C x y | throw "an empty disequality reason"
    let e := Node.eqNode a b
    if C.ee.nodes[x]! == e then return p
    -- the other orientation: the two equalities have the same rewrite
    let e' := C.ee.nodes[x]!
    if e' == Node.eqNode b a && Telos.rewrite e == Telos.rewrite e' then
      return .trans (.rw e) (.trans (.symm (.rw e')) p)
    throw "a disequality reason for the other orientation"


  /-- The arguments of a term, as the builder counts them. -/
  partial def children : Node → Array Node
    | .app _ cs => cs
    | _ => #[]
end

/-- The builder's context for the assumptions `A`, the explanation, among the
asserted literals `lits`. -/
def buildCtx (ee : EqualityEngine) (A : Array Node) (lits : Array Node) : BuildCtx :=
  { ee, index := A.zipIdx.foldl (fun m (l, i) => if m.contains ⟨l⟩ then m else m.insert ⟨l⟩ i) {},
    lits, owner := subtermOwners lits }

/-- Run the builder from the assumptions `A`: the assumptions it ends with. -/
def build (A : Array Node) (x : BuildM EqProof) : Except String (Array Node × EqProof) := do
  let (p, st) ← x.run { A, paths := subtermPaths A }
  return (st.A, p)

/-- A proof of `(t₁, t₂)` for terms of the engine. -/
def proveTerms (C : BuildCtx) (t₁ t₂ : Node) : BuildM EqProof := do
  let some i₁ := C.ee.nodeIds.get? ⟨t₁⟩ | throw "a term is not in the engine"
  let some i₂ := C.ee.nodeIds.get? ⟨t₂⟩ | throw "a term is not in the engine"
  let some p ← proveIds C i₁ i₂ | throw "identical terms"
  return p


/-- A certificate that a literal `lit`, explained by `E`, and the assumption
`neg` that makes it false are contradictory: assumptions (`E`, `neg`, and the
literals added by `pathTo`) and a proof of `(true, false)` from them. -/
def conflictOfPropagation (ee : EqualityEngine) (lits : Array Node) (E : Array Node) (lit neg : Node) :
    Except String (Array Node × EqProof) :=
  -- the premises of internal facts reach other asserted literals; the
  -- explanation's reasons that are internal facts are not assumptions
  let noFacts := ee.dt.facts.isEmpty && ee.sets.facts.isEmpty && ee.strings.facts.isEmpty
  let E := if noFacts then E else E.filter lits.contains
  let A := E.push neg
  let A := if noFacts then A else A ++ lits.filter (fun l => !A.contains l)
  let C := buildCtx ee A lits
  let n := E.size
  build A do
    match lit with
    | .app (.kind .NOT) #[.app (.kind .EQUAL) #[a, b]] =>
      -- the asserted (= a b), against the disequality
      let d ← proveDiseq C a b
      return EqProof.trans (.symm (.eqTrue (.assume n))) d
    | .app (.kind .NOT) #[x] =>
      -- x is asserted, and propagated false
      let q ← proveTerms C x Node.mkFalse
      return EqProof.trans (.symm (.assume n)) q
    | .app (.kind .EQUAL) #[a, b] =>
      let q ← proveTerms C a b
      return EqProof.trans (.symm (.eqTrue q)) (.assume n)
    | x =>
      let q ← proveTerms C x Node.mkTrue
      return EqProof.trans (.symm q) (.assume n)

/-- A certificate of the conflict of a merge of the constants `t₁` and `t₂`
(`true` and `false`), explained by `E`. -/
def conflictOfConstants (ee : EqualityEngine) (lits : Array Node) (E : Array Node) (t₁ t₂ : Node) :
    Except String (Array Node × EqProof) :=
  let C := buildCtx ee E lits
  build E do
    let p ← proveTerms C t₁ t₂
    if t₁ == Node.mkTrue && t₂ == Node.mkFalse then return p
    if t₁ == Node.mkFalse && t₂ == Node.mkTrue then return .symm p
    -- distinct values (strings, numbers): the rewriter evaluates their
    -- equality to `false`
    let e := Node.eqNode t₁ t₂
    if t₁.isConst && t₂.isConst && Telos.rewrite e == Node.mkFalse then
      return .trans (.symm (.eqTrue p)) (.rw e)
    throw "a merge of constants that are not distinct values"

/-- A proof of `(true, false)` from a proof `p` of `(x, b)` and one `q` of
`(x, c)`, for distinct Boolean constants `b` and `c`. -/
def contra (b : Bool) (p q : EqProof) : EqProof :=
  if b then .trans (.symm p) q else .trans (.symm q) p

/-- A certificate of a conflict of the theory of datatypes, from the asserted
literals `lits` (its assumptions). -/
def conflictOfDt (ee : EqualityEngine) (lits : Array Node) (cf : DT.Conflict) :
    Except String (Array Node × EqProof) :=
  let C := buildCtx ee lits lits
  build lits do
    let litProof (l : Node) : BuildM (Node × Bool × EqProof) := do
      let (atom, pol) := match l with
        | .app (.kind .NOT) #[a] => (a, false)
        | a => (a, true)
      let some p ← proveT C atom (Node.mkBool pol) | throw "a literal that is a constant"
      return (atom, pol, p)
    match cf.id with
    | "DATATYPES_CLASH_CONFLICT" =>
      let some e := cf.conf[0]? | throw "a clash without an equality"
      let .app (.kind .EQUAL) #[c₁, c₂] := e | throw "a clash without an equality"
      let some p ← proveT C c₁ c₂ | throw "a clash of identical terms"
      let lem := Node.eqNode e Node.mkFalse
      let v := EqProof.valid lem [DT.ruleStep .dt_cons_eq_clash lem]
      return .trans (.symm (.eqTrue p)) v
    | "DATATYPES_TESTER_CONFLICT" =>
      -- a tester of a term equal to a constructor term
      let some t := cf.conf[0]? | throw "a tester conflict without a tester"
      let some eq := cf.conf[1]? | throw "a tester conflict without an equality"
      let .app (.kind .EQUAL) #[x, c] := eq | throw "a tester conflict without an equality"
      let (atom, pol, p) ← litProof t
      let some (idx, _) := DT.isTester? atom | throw "a tester conflict without a tester"
      let some (T, ci, _) := DT.consApp? c | throw "a tester conflict without a constructor"
      let b := ci == idx
      if b == pol then throw "a tester conflict that is not one"
      let tc := DT.mkTester c T idx
      let v := EqProof.valid (Node.eqNode tc (Node.mkBool b)) [DT.ruleStep .dt_collapse_tester (Node.eqNode tc (Node.mkBool b))]
      let q := match ← proveT C x c with
        | some e => EqProof.trans (.congAt atom #[some e]) v
        | none => v
      return contra pol p q
    | "DATATYPES_TESTER_MERGE_CONFLICT" =>
      let some l₁ := cf.conf[0]? | throw "a tester conflict without testers"
      let some l₂ := cf.conf[1]? | throw "a tester conflict without testers"
      let (a₁, p₁, q₁) ← litProof l₁
      let (a₂, p₂, q₂) ← litProof l₂
      let some (i₁, x₁) := DT.isTester? a₁ | throw "a tester conflict without testers"
      let some (i₂, x₂) := DT.isTester? a₂ | throw "a tester conflict without testers"
      let e ← proveT C x₂ x₁
      if i₁ == i₂ then
        -- the same tester, with both values
        if p₁ == p₂ then throw "a tester conflict that is not one"
        let c := match e with
          | some e => EqProof.congAt a₂ #[some e]
          | none => EqProof.assume 0
        let q₂' := match e with
          | some _ => EqProof.trans (.symm c) q₂
          | none => q₂
        return contra p₁ q₁ q₂'
      -- two testers of different constructors, both true: instantiate the first
      if !p₁ || !p₂ then throw "a tester conflict that is not one"
      let some T := DT.dtType? x₁ | throw "a tester of a non-datatype"
      let I := DT.getInstCons x₁ T i₁
      let lemI := Node.eqNode a₁ (Node.eqNode x₁ I)
      let xI := EqProof.fromTrue (.trans (.symm (.valid lemI [DT.ruleStep .dt_inst lemI])) q₁)
      let e₂ := match e with
        | some e => EqProof.trans e xI
        | none => xI
      let tI := DT.mkTester I T i₂
      let lemC := Node.eqNode tI Node.mkFalse
      let vC := EqProof.valid lemC [DT.ruleStep .dt_collapse_tester lemC]
      return contra true q₂ (.trans (.congAt a₂ #[some e₂]) vC)
    | "DATATYPES_CYCLE" =>
      -- the term equal to a constructor term in which it occurs
      if cf.cycle.isEmpty then throw "a cycle without its path"
      let outer := cf.cycle.reverse
      let some (on, _, _) := outer[0]? | throw "a cycle without its path"
      let some (_, consIn, iIn) := outer.back? | throw "a cycle without its path"
      let some cIn := DT.consArgs consIn |>.bind (·[iIn]?) | throw "a cycle without its child"
      -- from the inside: a proof of `(child, Tⱼ)`
      let mut T := on
      let mut P : Option EqProof ← proveT C cIn on
      for k in [0:outer.size] do
        let (n, cons, i) := outer[outer.size - 1 - k]!
        let some cs := DT.consArgs cons | throw "a cycle without a constructor term"
        let args : Array (Option EqProof) := (Array.range cs.size).map fun j => if j == i then P else none
        let T' := match cons with
          | .app op _ => Node.app op (cs.set! i T)
          | t => t
        let Q := if P.isSome then some (EqProof.congAt cons args) else none
        let nc ← proveT C n cons
        P := match nc, Q with
          | some a, some b => some (.trans a b)
          | some a, none => some a
          | none, q => q
        T := T'
      let some P0 := P | throw "a cycle of a term with itself"
      let lem := Node.eqNode (Node.eqNode on T) Node.mkFalse
      let v := EqProof.valid lem [DT.ruleStep .dt_cycle lem]
      return .trans (.symm (.eqTrue P0)) v
    | id => throw s!"a conflict of {id} is not supported"

/-- A certificate of a conflict of the theory of sets, `conf` sent with the
identifier `id` (`Telos/Solver/Theory/Sets.lean`), from the literals `lits`. In
each, a membership is true of a set equal to one in which the rewriter decides
it false: `{x}` equal to the empty set (`SETS_EQ_CONFLICT`); a member of a set
equal to the empty set (`SETS_MEM_EQ_CONFLICT`, `SETS_EQ_MEM_CONFLICT`); a
member of a set whose membership rewrites to `false` (`SETS_DOWN_CLOSURE`). -/
def conflictOfSets (ee : EqualityEngine) (lits : Array Node) (id : String) (conf : Node) :
    Except String (Array Node × EqProof) :=
  let C := buildCtx ee lits lits
  build lits do
    let parts := match conf with
      | .app (.kind .AND) ps => ps
      | e => #[e]
    -- `(set.member x s)` true, `s` equal to `t`, and `(set.member x t)` false
    let memberConflict (atom t : Node) (pa : EqProof) : BuildM EqProof := do
      let .app (.kind .SET_MEMBER) #[x, s] := atom | throw "a conflict without a membership"
      let m' := Node.mkNode .SET_MEMBER #[x, t]
      if Telos.rewrite m' != Node.mkFalse then throw "a conflict the rewriter does not decide"
      let q : EqProof := match ← proveT C s t with
        | some ps => .trans (.symm (.congAt atom #[none, some ps])) pa
        | none => pa
      return .trans (.symm q) (.rw m')
    match id with
    | "SETS_EQ_CONFLICT" =>
      let .app (.kind .EQUAL) #[a, b] := conf | throw "a conflict without an equality"
      let (sg, e) := match a with
        | .app (.kind .SET_SINGLETON) _ => (a, b)
        | _ => (b, a)
      let .app (.kind .SET_SINGLETON) #[x] := sg | throw "a conflict without a singleton"
      let atom := Node.mkNode .SET_MEMBER #[x, sg]
      if Telos.rewrite atom != Node.mkTrue then throw "a conflict the rewriter does not decide"
      memberConflict atom e (.rw atom)
    | "SETS_MEM_EQ_CONFLICT" | "SETS_EQ_MEM_CONFLICT" | "SETS_DOWN_CLOSURE" =>
      let some atom := parts.find? fun l => match l with | .app (.kind .SET_MEMBER) _ => true | _ => false
        | throw "a conflict without a membership"
      let some (.app (.kind .EQUAL) #[_, t]) := parts.find? fun l => match l with
          | .app (.kind .EQUAL) _ => true
          | _ => false
        | throw "a conflict without an equality"
      let some pa ← proveT C atom Node.mkTrue | throw "a membership that is true"
      memberConflict atom t pa
    | id => throw s!"a conflict of {id} is not supported"

/-- A certificate of a conflict of the theory of strings, from the asserted
literals `lits` (its assumptions): its premises from the engine, and the CPC
proof of its inference `id` (`Telos/Solver/StringsCore.lean`). -/
def conflictOfStrings (ee : EqualityEngine) (lits : Array Node) (id : String) (premises : Array Node) :
    Except String (Array Node × EqProof) :=
  let C := buildCtx ee lits lits
  build lits do
    let ps ← premises.mapM (proveLitTrue C)
    let some q := StringsCore.proveFrom id premises ps Node.mkFalse
      | throw s!"a conflict of {id} without a proof"
    -- `(false, true)`, as `(true, false)`
    return .symm q

end Telos.Solver.EE
