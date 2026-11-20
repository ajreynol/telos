import Telos.Core.Node.PrintLet

/-!
# Theory events

The events at the interface of the theory solvers, as cvc5 prints them with
`-o theory-events` (the patch `cvc5-theory-events.patch`; the format is in
`docs/theory-engine-plan.md`). telos prints the same events, so that the two
traces can be compared (`scripts/fuzz-solve.py`).

Each event carries the SAT context level at which it happens. The terms are
printed as cvc5 prints them, with `let`s (`Node.toSmtLibLet`).
-/

namespace Telos.Solver

/-- cvc5's theories (`src/theory/theory_id.h`) that safe mode
(`--safe-mode=safe`) supports, in cvc5's order, which is the order in which the
theory engine runs their checks. The others (finite fields, floating point,
separation logic, bags) are not modelled. -/
inductive Theory where
  | THEORY_BUILTIN
  | THEORY_BOOL
  | THEORY_UF
  | THEORY_ARITH
  | THEORY_BV
  | THEORY_ARRAYS
  | THEORY_DATATYPES
  | THEORY_SETS
  | THEORY_STRINGS
  | THEORY_QUANTIFIERS
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Theory

/-- All theories, in cvc5's order. -/
def all : List Theory :=
  [THEORY_BUILTIN, THEORY_BOOL, THEORY_UF, THEORY_ARITH, THEORY_BV, THEORY_ARRAYS,
   THEORY_DATATYPES, THEORY_SETS, THEORY_STRINGS, THEORY_QUANTIFIERS]

def name : Theory → String
  | THEORY_BUILTIN => "THEORY_BUILTIN"
  | THEORY_BOOL => "THEORY_BOOL"
  | THEORY_UF => "THEORY_UF"
  | THEORY_ARITH => "THEORY_ARITH"
  | THEORY_BV => "THEORY_BV"
  | THEORY_ARRAYS => "THEORY_ARRAYS"
  | THEORY_DATATYPES => "THEORY_DATATYPES"
  | THEORY_SETS => "THEORY_SETS"
  | THEORY_STRINGS => "THEORY_STRINGS"
  | THEORY_QUANTIFIERS => "THEORY_QUANTIFIERS"

/-- Whether the theory has a `check` method (`TheoryTraits::hasCheck`): all
but the builtin and Boolean theories. -/
def hasCheck : Theory → Bool
  | THEORY_BUILTIN | THEORY_BOOL => false
  | _ => true

/-- The theory of the rewriter's `TheoryId`. -/
def ofTheoryId : TheoryId → Theory
  | .THEORY_BUILTIN => THEORY_BUILTIN
  | .THEORY_BOOL => THEORY_BOOL
  | .THEORY_ARITH => THEORY_ARITH
  | .THEORY_BV => THEORY_BV
  | .THEORY_UF => THEORY_UF
  | .THEORY_ARRAYS => THEORY_ARRAYS
  | .THEORY_SETS => THEORY_SETS
  | .THEORY_DATATYPES => THEORY_DATATYPES
  | .THEORY_STRINGS => THEORY_STRINGS
  | .THEORY_QUANTIFIERS => THEORY_QUANTIFIERS

end Theory

/-- The effort of a `check` call (`Theory::Effort`). -/
inductive Effort where
  | standard
  | full
  | lastCall
  deriving DecidableEq, Repr, Inhabited

def Effort.name : Effort → String
  | .standard => "EFFORT_STANDARD"
  | .full => "EFFORT_FULL"
  | .lastCall => "EFFORT_LAST_CALL"

/-- An event. Inference ids are cvc5's names (`InferenceId`, `IncompleteId`). -/
inductive Event where
  /-- An atom registered with the theory engine. -/
  | prereg (level : Nat) (t : Node)
  /-- A literal given to a theory. -/
  | assert (level : Nat) (T : Theory) (lit : Node)
  /-- A `check` call. -/
  | check (level : Nat) (T : Theory) (e : Effort)
  /-- The SAT context was popped, and is now at `level`. -/
  | pop (level : Nat)
  /-- An internal fact asserted to the equality engine, with its explanation. -/
  | fact (level : Nat) (T : Theory) (id : String) (lit exp : Node)
  | lemma (level : Nat) (T : Theory) (id : String) (lem : Node)
  /-- A conflict, as the conjunction of the conflicting literals. -/
  | conflict (level : Nat) (T : Theory) (id : String) (conj : Node)
  | propagate (level : Nat) (T : Theory) (lit : Node)
  /-- The explanation of a propagated literal, asked for by the SAT solver. -/
  | explain (level : Nat) (lit exp : Node)
  | phase (level : Nat) (lit : Node) (pol : Bool)
  | modelUnsound (level : Nat) (T : Theory) (id : String)
  | refutationUnsound (level : Nat) (T : Theory) (id : String)
  /-- The central equality engine's notifications (`-o theory-events-ee`). -/
  | eeNewClass (level : Nat) (t : Node)
  | eeMerge (level : Nat) (t₁ t₂ : Node)
  | eeDiseq (level : Nat) (t₁ t₂ reason : Node)
  deriving Inhabited

/-- The event with its nodes mapped by `f` (for naming skolems). -/
def Event.map (f : Node → Node) : Event → Event
  | .prereg k t => .prereg k (f t)
  | .assert k T l => .assert k T (f l)
  | .fact k T id l e => .fact k T id (f l) (f e)
  | .lemma k T id l => .lemma k T id (f l)
  | .conflict k T id c => .conflict k T id (f c)
  | .propagate k T l => .propagate k T (f l)
  | .explain k l e => .explain k (f l) (f e)
  | .phase k l p => .phase k (f l) p
  | .eeNewClass k t => .eeNewClass k (f t)
  | .eeMerge k a b => .eeMerge k (f a) (f b)
  | .eeDiseq k a b r => .eeDiseq k (f a) (f b) (f r)
  | e => e

/-- The event as cvc5 prints it, without the newline. -/
def Event.print (N : DtNames) : Event → String
  | .prereg k t => s!"(prereg {k} {t.toSmtLibLet N})"
  | .assert k T l => s!"(assert {k} {T.name} {l.toSmtLibLet N})"
  | .check k T e => s!"(check {k} {T.name} {e.name})"
  | .pop k => s!"(pop {k})"
  | .fact k T id l e => s!"(fact {k} {T.name} {id} {l.toSmtLibLet N} {e.toSmtLibLet N})"
  | .lemma k T id l => s!"(lemma {k} {T.name} {id} {l.toSmtLibLet N})"
  | .conflict k T id c => s!"(conflict {k} {T.name} {id} {c.toSmtLibLet N})"
  | .propagate k T l => s!"(propagate {k} {T.name} {l.toSmtLibLet N})"
  | .explain k l e => s!"(explain {k} {l.toSmtLibLet N} {e.toSmtLibLet N})"
  | .phase k l p => s!"(phase {k} {l.toSmtLibLet N} {p})"
  | .modelUnsound k T id => s!"(model-unsound {k} {T.name} {id})"
  | .refutationUnsound k T id => s!"(refutation-unsound {k} {T.name} {id})"
  | .eeNewClass k t => s!"(ee-new-class {k} {t.toSmtLibLet N})"
  | .eeMerge k a b => s!"(ee-merge {k} {a.toSmtLibLet N} {b.toSmtLibLet N})"
  | .eeDiseq k a b r => s!"(ee-diseq {k} {a.toSmtLibLet N} {b.toSmtLibLet N} {r.toSmtLibLet N})"

end Telos.Solver
