import Std.Data.HashSet
import Telos.Solver.EqProof
import Telos.Core.Node.FastType
import Telos.Core.Node.Print

/-!
# Certificates of the SAT solver's refutations

A refutation by the SAT solver and the theories is certified by its clauses,
as literals of terms (not SAT variables, so that the certificate does not
depend on the CNF stream's variables), each with its justification:
- **input**: it contains a clause of the CNF translation of an input formula
  (`inputClauses`, the top-level part of cvc5's `convertAndAssert`);
- **definition**: it contains a clause defining a connective's literal
  (`defClauses`, the Tseitin clauses of the CNF stream's `handle*`);
- **theory**: it contains the negation of each assumption of a certificate of
  a theory conflict (`EqProof.checkConflict`), as for conjunctions of literals;
- **lemma**: it contains a clause of the CNF translation of a theory lemma `F`
  (as the lemma's formula is given to the CNF stream, rewritten), for an
  `EqProof` of `(F, true)` from no assumptions, so that `F` is valid;

and the clauses the SAT solver learned, each a consequence of the clauses
before it by unit propagation (reverse unit propagation, `rup`), as is the
empty clause at the end. The functions here recompute what they check: the CNF
stream and the SAT solver are not trusted.

`verification/TelosProofs/Solver/SatProof.lean`: a certificate that checks
refutes the input formulas.
-/

open Eo Smtm SmtEval

namespace Telos.Solver.SatProof

/-- A clause: a disjunction of literals. -/
abbrev Clause := Array Node

/-- The literal of a formula `c` (negated with `neg`), as the CNF stream gives
it a SAT literal (`toCNF`): its negations are taken off. -/
def litOf (c : Node) (neg : Bool) : Node :=
  match c with
  | .app (.kind .NOT) cs => if h : cs.size = 1 then litOf cs[0] (!neg) else if neg then Node.notNode c else c
  | _ => if neg then Node.notNode c else c
termination_by sizeOf c
decreasing_by have := Array.sizeOf_getElem cs 0 (by omega); simp_wf; omega

/-- The connectives that the CNF stream translates (`Cnf.isConnective`), but
negation. -/
def isConn : Node → Bool
  | .app (.kind k) cs =>
    k == .AND || k == .OR || k == .XOR || k == .IMPLIES || k == .ITE ||
      (k == .EQUAL && cs[0]?.bind Node.typeHint == some .boolean)
  | _ => false

/-- The clauses that define the literal of the connective `n` in terms of its
children's (`handleAnd`, `handleOr`, …). -/
def defClauses (n : Node) : List (List Node) :=
  let p (c : Node) := litOf c false
  let q (c : Node) := negate (litOf c false)
  let ln := n
  let nn := Node.notNode n
  match n with
  | .app (.kind k) cs =>
    if k == .AND then (cs.toList.map fun c => [nn, p c]) ++ [cs.toList.map q ++ [ln]]
    else if k == .OR then (cs.toList.map fun c => [ln, q c]) ++ [cs.toList.map p ++ [nn]]
    else if h : k = .XOR ∧ cs.size = 2 then
      let a := cs[0]; let b := cs[1]
      [[p a, p b, nn], [q a, q b, nn], [p a, q b, ln], [q a, p b, ln]]
    else if h : k = .EQUAL ∧ cs.size = 2 then
      let a := cs[0]; let b := cs[1]
      [[q a, p b, nn], [p a, q b, nn], [q a, q b, ln], [p a, p b, ln]]
    else if h : k = .IMPLIES ∧ cs.size = 2 then
      let a := cs[0]; let b := cs[1]
      [[nn, q a, p b], [p a, ln], [q b, ln]]
    else if h : k = .ITE ∧ cs.size = 3 then
      let c := cs[0]; let t := cs[1]; let e := cs[2]
      [[nn, p t, p e], [nn, q c, p t], [nn, p c, p e], [ln, q t, q e], [ln, q c, q t], [ln, p c, q e]]
    else []
  | _ => []

/-- The clauses that asserting `n` (negated with `neg`) adds at the top level
(`convertAndAssert`): a conjunction is split, a disjunction is a clause, and so
on through the connectives; below, formulas are literals. -/
def inputClauses (n : Node) (neg : Bool) : List (List Node) :=
  match n with
  | .app (.kind k) cs =>
    if k == .AND then
      if !neg then (cs.attach.toList.map fun ⟨c, _⟩ => inputClauses c false).flatten
      else [cs.toList.map fun c => litOf c true]
    else if k == .OR then
      if !neg then [cs.toList.map fun c => litOf c false]
      else (cs.attach.toList.map fun ⟨c, _⟩ => inputClauses c true).flatten
    else if h : k = .XOR ∧ cs.size = 2 then
      if !neg then [[litOf cs[0] true, litOf cs[1] true], [litOf cs[0] false, litOf cs[1] false]]
      else [[litOf cs[0] true, litOf cs[1] false], [litOf cs[0] false, litOf cs[1] true]]
    else if h : k = .IMPLIES ∧ cs.size = 2 then
      if !neg then [[litOf cs[0] true, litOf cs[1] false]]
      else inputClauses cs[0] false ++ inputClauses cs[1] true
    else if h : k = .ITE ∧ cs.size = 3 then
      [[litOf cs[0] true, litOf cs[1] neg], [litOf cs[0] false, litOf cs[2] neg]]
    else if h : k = .NOT ∧ cs.size = 1 then inputClauses cs[0] (!neg)
    else if h : k = .EQUAL ∧ cs.size = 2 ∧ cs[0]!.typeHint = some .boolean then
      if !neg then [[litOf cs[0] true, litOf cs[1] false], [litOf cs[0] false, litOf cs[1] true]]
      else [[litOf cs[0] true, litOf cs[1] true], [litOf cs[0] false, litOf cs[1] false]]
    else [[litOf n neg]]
  | _ => [[litOf n neg]]
termination_by sizeOf n
decreasing_by
  all_goals
    simp_wf
    first
    | (have := Array.sizeOf_lt_of_mem ‹_›; omega)
    | (obtain ⟨_, h2⟩ := h; have := Array.sizeOf_getElem cs 0 (by omega); omega)
    | (obtain ⟨_, h2⟩ := h; have := Array.sizeOf_getElem cs 1 (by omega); omega)

/-- A clause contains another (as sets of literals). -/
def subsumes (d : List Node) (c : Clause) : Bool := d.all fun l => c.contains l

/-- The justification of a clause. -/
inductive Just where
  /-- A clause of the input formula at this index. -/
  | input (i : Nat)
  /-- A clause defining the connective `n`. -/
  | defn (n : Node)
  /-- The certificate `(A, p)` of a theory conflict: `p` proves `false` from
  the assumptions `A`, whose negations the clause contains. -/
  | theory (A : Array Node) (p : EqProof)
  /-- A clause of the CNF translation of the lemma `F`, which `p` proves
  (`(F, true)`) from no assumptions. -/
  | lemma (F : Node) (p : EqProof)
  deriving Inhabited

/-- A certificate of a refutation. -/
structure Cert where
  /-- The clauses given to the SAT solver, with their justifications. -/
  clauses : Array (Clause × Just)
  /-- The clauses it learned, in order. -/
  learned : Array Clause
  deriving Inhabited

/-- A literal is a formula (its Logos translation has type `Bool`). -/
def isBool (l : Node) : Bool := __smtx_typeof l.toSmt == .Bool

/-- The children of a node. -/
def children : Node → List Node
  | .app _ cs => cs.toList
  | _ => []

/-- A connective (or a negation) has the arity of its kind: two arguments or
more for `and` and `or`, three for `ite`, one for `not`, two for the others. -/
def arityOk : Node → Bool
  | .app (.kind k) cs =>
    if k == .AND || k == .OR then 2 ≤ cs.size
    else if k == .ITE then cs.size == 3
    else if k == .NOT then cs.size == 1
    else cs.size == 2
  | _ => false

/-- A connective or a negation (what `litOf` and `inputClauses` go through). -/
def isConnOrNot (n : Node) : Bool :=
  isConn n || match n with
    | .app (.kind .NOT) _ => true
    | _ => false

/-- The formula is Boolean, and so is each formula below it through the
connectives (and negations), which have their arities. -/
def boolTree (n : Node) : Bool :=
  isBool n && match n with
    | .app (.kind _) cs => !isConnOrNot n || (arityOk n && cs.attach.all fun ⟨c, _⟩ => boolTree c)
    | _ => true
termination_by sizeOf n
decreasing_by have := Array.sizeOf_lt_of_mem ‹_›; simp_wf; omega

/-- The justification of a clause checks, given the input formulas. -/
def Just.check (inputs : Array Node) (c : Clause) : Just → Bool
  | .input i => match inputs[i]? with
    | some f => boolTree f && (inputClauses f false).any (subsumes · c)
    | none => false
  | .defn n => isConn n && boolTree n && (defClauses n).any (subsumes · c)
  | .theory A p => EqProof.checkConflict A p && A.all isBool && A.all fun a => c.contains (negate a)
  | .lemma F p => EqProof.check #[] p == some (F, Node.mkTrue) && boolTree F &&
      (inputClauses F false).any (subsumes · c)

/-! ## Reverse unit propagation -/

/-- One pass of unit propagation over the clauses `db`, from the literals `S`
(true): a conflict (a clause whose literals are all false), or the literals
added (the last literal not false of a clause). -/
def propagatePass (db : Array Clause) (S : Std.HashSet Key) : Option (Std.HashSet Key) :=
  db.foldlM (init := S) fun S d =>
    let open_ := d.filter fun l => !S.contains ⟨negate l⟩
    if open_.isEmpty then none
    else if h : open_.size = 1 then some (S.insert ⟨open_[0]⟩)
    else some S

/-- Unit propagation to a conflict, within `fuel` passes. -/
def propagates (db : Array Clause) : Nat → Std.HashSet Key → Bool
  | 0, _ => false
  | f + 1, S =>
    match propagatePass db S with
    | none => true
    | some S' => if S'.size == S.size then false else propagates db f S'

/-- `c` follows from `db` by reverse unit propagation: assuming its literals
false propagates to a conflict. -/
def rup (db : Array Clause) (c : Clause) : Bool :=
  let S : Std.HashSet Key := c.foldl (fun S l => S.insert ⟨negate l⟩) {}
  propagates db (db.foldl (· + ·.size) 0 + c.size + 1) S

/-- Each learned clause follows from the clauses before it by unit
propagation, and so does the empty clause, from all of them. -/
def checkLearned (db : Array Clause) : List Clause → Bool
  | [] => rup db #[]
  | c :: cs => c.all isBool && rup db c && checkLearned (db.push c) cs

/-- **A certificate checks**: its clauses' justifications check, their literals
are formulas, and the learned clauses and then the empty clause follow by unit
propagation (`checkLearned`). -/
def Cert.check (inputs : Array Node) (cert : Cert) : Bool :=
  cert.clauses.all (fun (c, j) => c.all isBool && j.check inputs c) &&
    checkLearned (cert.clauses.map (·.1)) cert.learned.toList

/-- Why a certificate does not check (for diagnosis). -/
def Cert.why (inputs : Array Node) (cert : Cert) : String := Id.run do
  for (c, j) in cert.clauses do
    if !c.all isBool then return s!"a clause has a literal that is not a formula: {c.toList.map (Node.toSmtLib ·)}"
    if !j.check inputs c then
      let kind := match j with
        | .input i => s!"input {i}"
        | .defn n => s!"definition of {n.toSmtLib}"
        | .theory A _ => s!"theory, assumptions {A.toList.map (Node.toSmtLib ·)}"
        | .lemma F _ => s!"lemma {F.toSmtLib}"
      return s!"the justification ({kind}) of the clause {c.toList.map (Node.toSmtLib ·)} does not check"
  let mut db := cert.clauses.map (·.1)
  for (c, i) in cert.learned.zipIdx do
    if !(c.all isBool && rup db c) then
      return s!"learned clause {i} of {cert.learned.size} does not follow: {c.toList.map (Node.toSmtLib ·)}"
    db := db.push c
  return "the empty clause does not follow"

end Telos.Solver.SatProof
