import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Solver.EqualityEngine
import Telos.Solver.EqProof
import Telos.Solver.EqBuild

/-!
# Verified explanations

`EE.explainV`: the explanation of an equality, computed as cvc5's equality engine
computes it (`getExplanation`), with a theorem that it is sound
(`verification/TelosProofs/Solver/Explain.lean`): the reasons it returns imply
the equality. There is no separate certificate.

It follows the path that the breadth-first search of the equality graph finds
(`findPath`), from the end back to the start, as cvc5 does, and appends the
reasons in cvc5's order. Each edge is justified on the spot:
- an asserted edge by its reason, which must relate the edge's two terms
  (`EqProof.assumptionEq`);
- a congruence edge between two applications by the explanations of their
  arguments. The engine curries applications, so the prefixes of arguments,
  the internal nodes, are explained position by position (`qArgs`). The
  argument terms found must be those of the applications, which must be
  well typed: reached from an input literal (a root) along a path of operators
  whose children are well typed when they are (`EqProof.follow`);
- a reflexivity edge, of `(= a b)` with `true`, by the explanation of `a` and
  `b`;
- an edge of evaluated constants is not supported: the explanation fails.

These checks are local and cost a constant (or the number of arguments) per
edge. Whatever path the search returns, and whatever the engine's state, an
explanation that succeeds is sound: the theorem does not depend on invariants
of the engine.

Recursion is bounded by a fuel. Completed queries are cached, as cvc5 caches
them; cvc5 also caches the queries in progress, which differs only on cyclic
queries, which cannot happen since cvc5's equality graph is a forest.
-/

namespace Telos.Solver.EE

open Telos.Solver

/-- What an argument position of a congruence proves: nothing (the same
argument on both sides, up to the path), or that two terms are equal. -/
inductive Rel where
  | same
  | eq (a b : Node)
  deriving Inhabited, BEq

/-- Compose the relations of an argument position along a path. -/
def Rel.compose : Rel → Rel → Option Rel
  | .same, r => some r
  | r, .same => some r
  | .eq a b, .eq c d => if b == c then some (.eq a d) else none

def composeAll : List Rel → List Rel → Option (List Rel)
  | [], [] => some []
  | r :: rs, q :: qs => do
    let x ← r.compose q
    let xs ← composeAll rs qs
    return x :: xs
  | _, _ => none

structure ExState where
  /-- The reasons, in order. -/
  out : Array Node := #[]
  fullCache : Std.HashSet (Nat × Nat) := {}
  argsCache : Std.HashMap (Nat × Nat) (List Rel) := {}
  deriving Inhabited

def ExState.empty : ExState := { out := #[], fullCache := {}, argsCache := {} }

abbrev ExM := StateT ExState Option

/-- Fail (`failure`, as a plain function, which is simpler to reason about). -/
def fail {α : Type} : ExM α := fun _ => none

/-- What an explanation reads: the engine, the roots (input literals, for the
typing of applications), and a path below a root to each of their subterms. -/
structure ExCtx where
  ee : EqualityEngine
  roots : Array Node
  paths : Std.HashMap Key SubPath

def ExCtx.node (C : ExCtx) (i : Nat) : Node := C.ee.nodes[i]!

def ExCtx.app (C : ExCtx) (i : Nat) : Option FunApp := (C.ee.apps[i]!).map (·.1)

/-- `t` is reached from a root along a path of operators whose children are
well typed when they are. -/
def ExCtx.typedBelowRoot (C : ExCtx) (t : Node) : Bool :=
  match C.paths.get? ⟨t⟩ with
  | some p => match C.roots[p.root]? with
    | some r => EqProof.follow r p.path == some t
    | none => false
  | none => false

/-- The path is a chain from `x` to `y`. -/
def chainOk : Nat → List (Nat × Nat × Edge) → Nat → Bool
  | x, [], y => x == y
  | x, (c, n, _) :: rest, y => x == c && chainOk n rest y

/-- The relations of the arguments of two applications `t = (op cs)` and
`s = (op ds)` are those of their arguments. -/
def argsMatch (cs ds : Array Node) (rs : List Rel) : Bool :=
  rs.length == cs.size && cs.size == ds.size &&
    (List.range cs.size).all fun i =>
      match rs[i]?, cs[i]?, ds[i]? with
      | some .same, some c, some d => c == d
      | some (.eq a b), some c, some d => a == c && b == d
      | _, _, _ => false

mutual
  /-- Explain the equality of the terms of the nodes `x` and `y`. -/
  def qFull (C : ExCtx) : Nat → Nat → Nat → ExM Unit
    | 0, _, _ => fail
    | n + 1, x, y => do
      if x == y then return
      if (← get).fullCache.contains (x, y) then return
      let some path := findPath C.ee x y | fail
      if !chainOk x path.toList y then fail
      stepsFull C n path.toList.reverse
      modify fun s => { s with fullCache := s.fullCache.insert (x, y) }
  termination_by n => (n, 1, 0)

  /-- The relations of the first arguments of two applications with `k`
  arguments, from their first parts `f₁.a` and `f₂.a`: the left side of an
  equality, the operator (for one argument), or the prefix. -/
  def preArgs (C : ExCtx) (n : Nat) (f₁ f₂ : FunApp) (k : Nat) : ExM (List Rel) :=
    match f₁.type with
    | .equality => do
      qFull C n f₁.a f₂.a
      return [if f₁.a == f₂.a then Rel.same else .eq (C.node f₁.a) (C.node f₂.a)]
    | _ =>
      if k == 1 then
        if f₁.a == f₂.a then pure [] else fail
      else qArgs C n f₁.a f₂.a
  termination_by (n, 2, 0)

  /-- The steps of a path between terms, the last first. -/
  def stepsFull (C : ExCtx) (n : Nat) : List (Nat × Nat × Edge) → ExM Unit
    | [] => pure ()
    | (cur, next, e) :: rest => do
      edgeFull C n cur next e
      stepsFull C n rest
  termination_by l => (n, 4, l.length)

  /-- One edge between the terms of `cur` and `next`. -/
  def edgeFull (C : ExCtx) (n : Nat) (cur next : Nat) (e : Edge) : ExM Unit :=
    match e.type with
    | .equality => do
      let ab := EqProof.assumptionEq e.reason
      if ab == (C.node cur, C.node next) || ab == (C.node next, C.node cur) then
        modify fun s => { s with out := s.out.push e.reason }
      else fail
    | .congruence => do
      let some f₁ := C.app cur | fail
      let some f₂ := C.app next | fail
      let t := C.node cur
      let u := C.node next
      let .app op cs := t | fail
      let .app op' ds := u | fail
      if op != op' then fail
      if !(op.eoShape.substCongruent && op.childrenTypedOfParent) then fail
      if !C.typedBelowRoot t then fail
      -- the arguments: a prefix (or the operator, or the left side of an
      -- equality), and the last
      let pre ← preArgs C n f₁ f₂ cs.size
      qFull C n f₁.b f₂.b
      let last := if f₁.b == f₂.b then Rel.same else .eq (C.node f₁.b) (C.node f₂.b)
      if !argsMatch cs ds (pre ++ [last]) then fail
    | .reflexivity => do
      let eqId := if cur == C.ee.trueId then next else cur
      let some f := C.app eqId | fail
      if f.type != .equality then fail
      if C.node C.ee.trueId != Node.mkTrue then fail
      if C.node eqId != Node.eqNode (C.node f.a) (C.node f.b) then fail
      if !C.typedBelowRoot (C.node eqId) then fail
      if !(cur == C.ee.trueId || next == C.ee.trueId) then fail
      qFull C n f.a f.b
    | .constants => fail
  termination_by (n, 3, 0)

  /-- Explain the equality of the argument prefixes of the internal nodes `x`
  and `y`: the relation of each position. -/
  def qArgs (C : ExCtx) : Nat → Nat → Nat → ExM (List Rel)
    | 0, _, _ => fail
    | n + 1, x, y => do
      if let some rs := (← get).argsCache.get? (x, y) then return rs
      let some path := findPath C.ee x y | fail
      if !chainOk x path.toList y then fail
      let steps ← stepsArgs C n path.toList.reverse
      -- compose the steps, from the start of the path
      let some first := steps.getLast? | fail
      let some rs := steps.dropLast.foldr (fun st acc => acc.bind fun a => composeAll a st) (some first)
        | fail
      modify fun s => { s with argsCache := s.argsCache.insert (x, y) rs }
      return rs
  termination_by n => (n, 1, 0)

  /-- The steps of a path between internal nodes, the last first. -/
  def stepsArgs (C : ExCtx) (n : Nat) : List (Nat × Nat × Edge) → ExM (List (List Rel))
    | [] => pure []
    | (cur, next, e) :: rest => do
      let r ← edgeArgs C n cur next e
      let rs ← stepsArgs C n rest
      return r :: rs
  termination_by l => (n, 4, l.length)

  /-- One congruence edge between internal nodes: the relation of each
  argument position. -/
  def edgeArgs (C : ExCtx) (n : Nat) (cur next : Nat) (e : Edge) : ExM (List Rel) := do
    if e.type != .congruence then fail
    let some f₁ := C.app cur | fail
    let some f₂ := C.app next | fail
    let pre ← if (C.app f₁.a).isSome then qArgs C n f₁.a f₂.a
      else if f₁.a == f₂.a then pure [] else fail
    qFull C n f₁.b f₂.b
    let last := if f₁.b == f₂.b then Rel.same else .eq (C.node f₁.b) (C.node f₂.b)
    return pre ++ [last]
  termination_by (n, 3, 0)
end

/-- Enough fuel for the explanations of an engine: the depth of the recursion
is at most its number of nodes (cvc5's equality graph is a forest, and each
recursion goes to older edges). -/
def ExCtx.fuel (C : ExCtx) : Nat := C.ee.nodes.size + 2

/-- The context of the explanations of `ee`, with the roots `roots`. -/
def exCtx (ee : EqualityEngine) (roots : Array Node) : ExCtx :=
  { ee, roots, paths := subtermPaths roots }

/-- The atom and polarity of a literal. -/
def litAtom (lit : Node) : Node × Bool :=
  match lit with
  | .app (.kind .NOT) cs => if h : cs.size = 1 then (cs[0], false) else (lit, true)
  | _ => (lit, true)

/-- Run a query from the empty state: its reasons, without duplicates, in
order. -/
def runFull (C : ExCtx) (x y : Nat) : Option (Array Node) := do
  let ((), st) ← qFull C C.fuel x y ExState.empty
  return st.out.foldl (fun acc a => if acc.contains a then acc else acc.push a) #[]

/-- The reasons of `(= l r)`. -/
def explainEqV (C : ExCtx) (l r : Node) : Option (Array Node) :=
  match C.ee.nodeIds.get? ⟨l⟩, C.ee.nodeIds.get? ⟨r⟩ with
  | some i, some j => if C.node i == l && C.node j == r && l != r then runFull C i j else none
  | _, _ => none

/-- The reasons of `(not (= l r))`: a disequality propagated by a trigger, the
merge of the equality with `false`. -/
def explainDiseqV (C : ExCtx) (l r : Node) : Option (Array Node) :=
  match C.ee.nodeIds.get? ⟨l⟩, C.ee.nodeIds.get? ⟨r⟩ with
  | some i, some j =>
    match C.ee.diseqReasons.get? (i, j) with
    | some (lo, hi) =>
      match C.ee.deducedReasons[lo]? with
      | some (x, y) =>
        if hi == lo + 1 && C.node x == Node.eqNode l r && C.node y == Node.mkFalse then runFull C x y
        else none
      | none => none
    | none => none
  | _, _ => none

/-- The reasons of a predicate's value. -/
def explainPredV (C : ExCtx) (atom : Node) (pol : Bool) : Option (Array Node) :=
  match C.ee.nodeIds.get? ⟨atom⟩ with
  | some i =>
    let b := if pol then C.ee.trueId else C.ee.falseId
    if C.node b == Node.mkBool pol && C.node i == atom && i != b then runFull C i b else none
  | none => none

/-- The explanation of a literal, as cvc5's proof equality engine computes it
(`ProofEqEngine::explainWithProof`, as `EE.explainLit`): its reasons, without
duplicates, in order; `none` if the verified explanation does not apply (a
reflexive equality, a disequality from several reasons, a merge of evaluated
constants, or a failed check). -/
def explainLitV (C : ExCtx) (lit : Node) : Option (Array Node) :=
  let (atom, pol) := litAtom lit
  match atom with
  | .app (.kind .EQUAL) cs =>
    if h : cs.size = 2 then
      if pol then explainEqV C cs[0] cs[1] else explainDiseqV C cs[0] cs[1]
    else explainPredV C atom pol
  | _ => explainPredV C atom pol

end Telos.Solver.EE
