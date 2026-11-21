import Std.Data.HashMap
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Solver.Sat.Basic

/-!
# The CNF stream

A port of cvc5's CNF stream as it runs with proofs on (`ProofCnfStream`,
`src/prop/proof_cnf_stream.cpp`, over `CnfStream`, `src/prop/cnf_stream.cpp`):
the Tseitin translation of formulas into clauses over SAT literals. Each
Boolean connective gets a literal, defined by clauses; each atom gets one too,
and a theory atom (or a Boolean term skolem) is announced to the host when it
gets its literal, which cvc5's `TheoryPreregistrar` turns into its eager
preregistration.

The stream knows terms and SAT literals, but neither the SAT solver nor the
theory engine. What it asks of the SAT solver (new variables, clauses) is
queued as `SatOp`s, which the host gives to the SAT solver in order; the
stream predicts the variables' indices. That is equivalent to cvc5's direct
calls: the translation never reads the SAT solver's assignment, and the
clauses a theory adds during the search are lemmas, which MiniSat only queues.
-/

namespace Telos.Solver.Cnf

open Telos.Sat

/-- Where a clause comes from, for the certificate of a refutation
(`Telos/Solver/SatProof.lean`). -/
inductive ClauseTag where
  /-- Asserting the formula of this source (`State.src`), at the top level. -/
  | src (i : Nat)
  /-- The definition of the literal of the connective `n`. -/
  | defn (n : Node)
  deriving Inhabited

/-- A request to the SAT solver. -/
inductive SatOp where
  /-- A new variable (the next index), a theory atom or not. -/
  | newVar (isTheoryAtom : Bool)
  /-- A clause, removable or not. -/
  | clause (lits : Array Lit) (removable : Bool) (tag : ClauseTag)
  /-- Prefer a phase for the variable of the literal, its sign
  (`preferPhase`: MiniSat's `freezePolarity`). -/
  | phase (lit : Lit)
  deriving Inhabited

structure State where
  /-- The literal of each atom and connective that has one (cvc5 maps their
  negations too; here `getLiteral` negates). -/
  nodeToLit : Std.HashMap Key Lit := {}
  /-- The node of each literal (`d_literalToNodeMap`, by `Lit.x`). -/
  litToNode : Std.HashMap Nat Node := {}
  /-- The number of SAT variables, those of `true` and `false` included. -/
  nVars : Nat := 2
  /-- The requests to the SAT solver not yet given to it. -/
  ops : Array SatOp := #[]
  /-- The Boolean variables (`d_booleanVariables`), in order. -/
  booleanVariables : Array Node := #[]
  /-- The clauses being added are removable (`d_removable`). -/
  removable : Bool := false
  /-- The source of the formula being asserted (for `ClauseTag.src`). -/
  src : Nat := 0
  deriving Inhabited

/-- What the stream asks of its host (cvc5's `Registrar`, and `Env`). -/
structure Host (m : Type → Type) where
  /-- A theory atom got its literal (`notifySatLiteral`). -/
  notifySatLiteral : Node → m Unit
  /-- A Boolean variable that is not a Boolean term skolem: the SAT solver's
  own, not a theory atom. -/
  isInternalBoolVar : Node → Bool

def trueLit : Lit := Lit.mk 0
def falseLit : Lit := Lit.mk 1

/-- A Boolean connective that the stream translates (rather than an atom). -/
def isConnective : Node → Bool
  | .app (.kind k) cs =>
    k == .NOT || k == .AND || k == .OR || k == .XOR || k == .IMPLIES || k == .ITE ||
      (k == .EQUAL && cs[0]?.bind Node.typeHint == some .boolean)
  | _ => false

variable {m : Type → Type} [Monad m] [MonadStateOf State m]

@[inline] def cnf : m State := getThe State

def hasLiteral (n : Node) : m Bool := do return (← cnf).nodeToLit.contains ⟨n⟩

/-- The literal of a node, a negation included; `none` if it has none. -/
def getLiteral? (s : State) (n : Node) : Option Lit :=
  match n with
  | .app (.kind .NOT) #[a] =>
    match s.nodeToLit.get? ⟨n⟩ with
    | some l => some l
    | none => (s.nodeToLit.get? ⟨a⟩).map (·.neg)
  | _ => s.nodeToLit.get? ⟨n⟩

/-- The node of a literal (`getNode`). -/
def getNode? (s : State) (l : Lit) : Option Node := s.litToNode.get? l.x

/-- `assertClause`: duplicate literals dropped, the clause goes to the SAT
solver. -/
def assertClause (c : Array Lit) (defn : Option Node := none) : m Unit :=
  modifyThe State fun s => Id.run do
    let mut out : Array Lit := #[]
    for l in c do
      if !out.contains l then out := out.push l
    let ops := s.ops
    let s := { s with ops := #[] }
    let tag := match defn with
      | some n => ClauseTag.defn n
      | none => .src s.src
    return { s with ops := ops.push (.clause out s.removable tag) }

section
variable (H : Host m)

/-- `newLiteral`: the literal of `node`, made if it has none, mapped back to
`node`; a theory atom is announced to the host. -/
def newLiteral (node : Node) (isTheoryAtom : Bool := false) (notifyTheory : Bool := false) : m Lit := do
  let lit ← modifyGetThe State fun s =>
    match s.nodeToLit.get? ⟨node⟩ with
    | some l => (l, s)
    | none =>
      let (l, s) := match node with
        | .const (.boolean true) => (trueLit, s)
        | .const (.boolean false) => (falseLit, s)
        | _ =>
          let ops := s.ops
          let s := { s with ops := #[] }
          (Lit.mk s.nVars, { s with nVars := s.nVars + 1, ops := ops.push (.newVar isTheoryAtom) })
      let map := s.nodeToLit
      let s := { s with nodeToLit := {} }
      (l, { s with nodeToLit := map.insert ⟨node⟩ l })
  -- (the policy is `TRACK`: every literal is mapped back)
  modifyThe State fun s =>
    let back := s.litToNode
    let s := { s with litToNode := {} }
    let back := if back.contains lit.x then back else back.insert lit.x node
    let back := if back.contains lit.neg.x then back else back.insert lit.neg.x (Node.notNode node)
    { s with litToNode := back }
  if notifyTheory then
    -- a lemma may be added meanwhile: the flag is restored
    let removable := (← cnf).removable
    let src := (← cnf).src
    H.notifySatLiteral node
    modifyThe State fun s => { s with removable, src }
  return lit

/-- `convertAtom`: an atom gets its literal; a theory atom (anything but a
Boolean variable of the SAT solver) is announced. -/
def convertAtom (node : Node) : m Lit := do
  if H.isInternalBoolVar node then
    modifyThe State fun s => { s with booleanVariables := s.booleanVariables.push node }
    newLiteral H node false false
  else
    newLiteral H node true true

mutual

/-- `toCNF`: the literal of a formula, its connectives translated (children
first, left to right). -/
partial def toCNF (node : Node) (negated : Bool := false) : m Lit := do
  if let some l := (← cnf).nodeToLit.get? ⟨node⟩ then
    return if negated then l.neg else l
  let lit ← match node with
    | .app (.kind .AND) cs => handleAnd node cs
    | .app (.kind .OR) cs => handleOr node cs
    | .app (.kind .XOR) #[a, b] => handleXor node a b
    | .app (.kind .IMPLIES) #[a, b] => handleImplies node a b
    | .app (.kind .ITE) #[c, t, e] => handleIte node c t e
    | .app (.kind .NOT) #[a] => do pure (← toCNF a).neg
    | .app (.kind .EQUAL) #[a, b] =>
      if a.typeHint == some .boolean then handleIff node a b else convertAtom H node
    | _ => convertAtom H node
  return if negated then lit.neg else lit

partial def handleAnd (node : Node) (cs : Array Node) : m Lit := do
  let mut clause : Array Lit := #[]
  for c in cs do clause := clause.push (← toCNF c).neg
  let lit ← newLiteral H node
  for c in clause do assertClause #[lit.neg, c.neg] (some node)
  assertClause (clause.push lit) (some node)
  return lit

partial def handleOr (node : Node) (cs : Array Node) : m Lit := do
  let mut clause : Array Lit := #[]
  for c in cs do clause := clause.push (← toCNF c)
  let lit ← newLiteral H node
  for c in clause do assertClause #[lit, c.neg] (some node)
  assertClause (clause.push lit.neg) (some node)
  return lit

partial def handleXor (node a b : Node) : m Lit := do
  let a ← toCNF a
  let b ← toCNF b
  let lit ← newLiteral H node
  assertClause #[a, b, lit.neg] (some node)
  assertClause #[a.neg, b.neg, lit.neg] (some node)
  assertClause #[a, b.neg, lit] (some node)
  assertClause #[a.neg, b, lit] (some node)
  return lit

partial def handleIff (node a b : Node) : m Lit := do
  let a ← toCNF a
  let b ← toCNF b
  let lit ← newLiteral H node
  assertClause #[a.neg, b, lit.neg] (some node)
  assertClause #[a, b.neg, lit.neg] (some node)
  assertClause #[a.neg, b.neg, lit] (some node)
  assertClause #[a, b, lit] (some node)
  return lit

partial def handleImplies (node a b : Node) : m Lit := do
  let a ← toCNF a
  let b ← toCNF b
  let lit ← newLiteral H node
  assertClause #[lit.neg, a.neg, b] (some node)
  assertClause #[a, lit] (some node)
  assertClause #[b.neg, lit] (some node)
  return lit

partial def handleIte (node c t e : Node) : m Lit := do
  let c ← toCNF c
  let t ← toCNF t
  let e ← toCNF e
  let lit ← newLiteral H node
  assertClause #[lit.neg, t, e] (some node)
  assertClause #[lit.neg, c.neg, t] (some node)
  assertClause #[lit.neg, c, e] (some node)
  assertClause #[lit, t.neg, e.neg] (some node)
  assertClause #[lit, c.neg, t.neg] (some node)
  assertClause #[lit, c, e.neg] (some node)
  return lit

end

/-- `convertAndAssert`: assert `node` (or its negation): a top-level
conjunction is split, a top-level disjunction is one clause, and so on down
the connectives; below them, formulas get their literals. -/
partial def convertAndAssertRec (node : Node) (negated : Bool) : m Unit := do
  match node with
  | .app (.kind .AND) cs =>
    if !negated then
      for c in cs do convertAndAssertRec c false
    else
      let mut clause : Array Lit := #[]
      for c in cs do clause := clause.push (← toCNF H c true)
      assertClause clause
  | .app (.kind .OR) cs =>
    if !negated then
      let mut clause : Array Lit := #[]
      for c in cs do clause := clause.push (← toCNF H c false)
      assertClause clause
    else
      for c in cs do convertAndAssertRec c true
  | .app (.kind .XOR) #[a, b] =>
    let p ← toCNF H a
    let q ← toCNF H b
    if !negated then
      assertClause #[p.neg, q.neg]
      assertClause #[p, q]
    else
      assertClause #[p.neg, q]
      assertClause #[p, q.neg]
  | .app (.kind .IMPLIES) #[a, b] =>
    if !negated then
      let p ← toCNF H a
      let q ← toCNF H b
      assertClause #[p.neg, q]
    else
      convertAndAssertRec a false
      convertAndAssertRec b true
  | .app (.kind .ITE) #[c, t, e] =>
    let p ← toCNF H c
    let q ← toCNF H t negated
    let r ← toCNF H e negated
    assertClause #[p.neg, q]
    assertClause #[p, r]
  | .app (.kind .NOT) #[a] => convertAndAssertRec a (!negated)
  | .app (.kind .EQUAL) #[a, b] =>
    if a.typeHint == some .boolean then
      let p ← toCNF H a
      let q ← toCNF H b
      if !negated then
        assertClause #[p.neg, q]
        assertClause #[p, q.neg]
      else
        assertClause #[p.neg, q.neg]
        assertClause #[p, q]
    else assertClause #[← toCNF H node negated]
  | _ => assertClause #[← toCNF H node negated]

/-- `convertAndAssert`, with the clauses removable or not. -/
def convertAndAssert (node : Node) (removable : Bool) (negated : Bool := false) (src : Nat := 0) : m Unit := do
  modifyThe State fun s => { s with removable, src }
  convertAndAssertRec H node negated

/-- `ensureLiteral`: a node gets a literal, unless it has one; a connective is
translated (its definition clauses are not removable), an atom announced. -/
def ensureLiteral (n : Node) : m Unit := do
  let n := match n with
    | .app (.kind .NOT) #[a] => a
    | _ => n
  if ← hasLiteral n then return
  if isConnective n then
    modifyThe State fun s => { s with removable := false }
    let _ ← toCNF H n false
  else
    let _ ← convertAtom H n

/-- `PropEngine::preferPhase`: the SAT solver is to prefer `n` with the phase
`pol` (it has a literal). -/
def preferPhase (n : Node) (pol : Bool) : m Unit := do
  if let some l := getLiteral? (← cnf) n then
    modifyThe State fun s => { s with ops := s.ops.push (.phase (if pol then l else l.neg)) }

end

/-- Take the requests to the SAT solver. -/
def takeOps : m (Array SatOp) := modifyGetThe State fun s => (s.ops, { s with ops := #[] })

end Telos.Solver.Cnf
