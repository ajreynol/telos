import Std.Data.HashMap
import Telos.Solver.EqualityEngine
import Telos.Solver.EqProof

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
      let some i := C.index.get? ⟨edge.reason⟩ | throw "a reason is not an assumption"
      let (x, y) := EqProof.assumptionEq edge.reason
      if x == a && y == b then return .assume i
      if x == b && y == a then return .symm (.assume i)
      throw "a reason does not match its edge"
    | .congruence =>
      let src ← pathTo C a
      let args ← appArgs C cur next
      return .cong src args
    | .reflexivity =>
      let eqId := if cur == ee.trueId then next else cur
      let some (f, _) := ee.apps[eqId]! | throw "a reflexivity edge without an equality"
      let some p ← proveIds C f.a f.b | throw "a reflexivity of identical terms"
      let q := EqProof.eqTrue p
      return if cur == ee.trueId then .symm q else q
    | .constants => throw "merges of evaluated constants are not supported"

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

/-- A proof of `((= a b), false)`, from the reasons of the propagated
disequality of `a` and `b`. Only a disequality propagated by a trigger (whose
reason is the merge of the equality with `false`) is supported. -/
def proveDiseq (C : BuildCtx) (a b : Node) : BuildM EqProof := do
  let some i := C.ee.nodeIds.get? ⟨a⟩ | throw "a term is not in the engine"
  let some j := C.ee.nodeIds.get? ⟨b⟩ | throw "a term is not in the engine"
  let some (lo, hi) := C.ee.diseqReasons.get? (i, j) | throw "no reasons for a disequality"
  if hi != lo + 1 then throw "a disequality from several reasons is not supported"
  let (x, y) := C.ee.deducedReasons[lo]!
  if y != C.ee.falseId then throw "a disequality reason is not a merge with false"
  let some p ← proveIds C x y | throw "an empty disequality reason"
  if C.ee.nodes[x]! == Node.eqNode a b then return p
  throw "a disequality reason for the other orientation"

/-- A certificate that a literal `lit`, explained by `E`, and the assumption
`neg` that makes it false are contradictory: assumptions (`E`, `neg`, and the
literals added by `pathTo`) and a proof of `(true, false)` from them. -/
def conflictOfPropagation (ee : EqualityEngine) (lits : Array Node) (E : Array Node) (lit neg : Node) :
    Except String (Array Node × EqProof) :=
  let A := E.push neg
  let C := buildCtx ee A lits
  let n := A.size - 1
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
    throw "a merge of constants other than true and false"

end Telos.Solver.EE
