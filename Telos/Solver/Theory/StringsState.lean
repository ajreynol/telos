import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key

/-!
# The state of the theory of strings

The state of cvc5's `TheoryStrings` (`src/theory/strings/`): its `SolverState`
and `EqcInfo`, its `TermRegistry`, and its inference manager, as data. Like the
states of datatypes and sets, it is a field of the central equality engine
(`EqualityEngine.strings`), because the theory reacts to the engine's
notifications while it propagates.

The parts on the SAT context are undone on backtracking through a trail
(`Undo`): the preregistered terms (`d_preregisteredTerms`), the function terms
(`d_functionsTerms`), the information of the classes (`EqcInfo`, whose fields
are `CDO`s), and the disequalities (`d_ee_disequalities`). The parts on the user
context (the registered terms and types, the proxy variables and their lengths,
the terms whose length lemmas were sent, the lemma cache) are not.
-/

namespace Telos.Solver.Strings

instance : Inhabited Key := ⟨⟨default⟩⟩

/-- `EqcInfo`: its fields are context dependent. -/
structure EqcInfo where
  /-- A length term of the class (`d_lengthTerm`). -/
  lengthTerm : Option Node := none
  /-- A term whose code is in the class (`d_codeTerm`). -/
  codeTerm : Option Node := none
  /-- `d_cardinalityLemK`. -/
  cardinalityLemK : Nat := 0
  /-- `d_normalizedLength`. -/
  normalizedLength : Option Node := none
  /-- The eager solver's bounds (`d_firstBound`, `d_secondBound`): the terms
  that explain the longest constant prefix and suffix of the class. -/
  firstBound : Option Node := none
  secondBound : Option Node := none
  deriving Inhabited

/-- A pending lemma or fact of the inference manager (`InferInfo`, sent as a
lemma or asserted as a fact). -/
structure Inference where
  id : String
  conc : Node
  /-- The explanation, as literals. -/
  exp : Array Node := #[]
  /-- The part of the explanation that is not in the equality engine
  (`d_noExplain`). -/
  noExplain : Array Node := #[]
  deriving Inhabited

/-- An entry of the trail. -/
inductive Undo where
  | prereg (k : Key)
  | eqcInfo (k : Key) (old : Option EqcInfo)
  | pendingConflict
  deriving Inhabited

structure State where
  /-- The theory is enabled. -/
  enabled : Bool := false
  /-- `d_preregisteredTerms` (context dependent). -/
  preregistered : Std.HashSet Key := {}
  /-- `d_functionsTerms` (context dependent). -/
  functionTerms : Array Node := #[]
  /-- `d_eqcInfo` (context dependent). -/
  eqcInfo : Std.HashMap Key EqcInfo := {}
  /-- `d_ee_disequalities`: the disequalities of strings asserted, in order
  (context dependent). -/
  disequalities : Array Node := #[]
  /-- `d_registeredTerms`, `d_registeredTypes` (user context). -/
  registered : Std.HashSet Key := {}
  registeredTypes : Array TypeNode := #[]
  /-- `d_proxyVar`, `d_proxyVarToLength` (user context). -/
  proxyVar : Std.HashMap Key Node := {}
  proxyVarToLength : Std.HashMap Key Node := {}
  /-- `d_lengthLemmaTermsCache` (user context). -/
  lengthLemmaTerms : Std.HashSet Key := {}
  /-- `d_inputVars` (user context). -/
  inputVars : Std.HashSet Key := {}
  /-- The inference manager's pending facts and lemmas. -/
  pendingFacts : Array Inference := #[]
  pendingLemmas : Array Inference := #[]
  /-- `d_numCurrentFacts`, `d_numCurrentLemmas` since the last `reset`. -/
  sentFacts : Nat := 0
  sentLemmas : Nat := 0
  /-- `d_lemmasSent`, by rewritten lemma (user context). -/
  lemmaCache : Std.HashSet Key := {}
  /-- The internal facts asserted, with their inference and explanation, for the
  certificates. -/
  facts : Std.HashMap Key (String × Node) := {}
  /-- `d_pendingConflict` (context dependent): a conflict found while the
  equality engine merges (the eager solver's), sent after the fact: its
  inference, and its premises. -/
  pendingConflict : Option (String × Array Node) := none
  /-- The last conflict of the theory: its inference and the conflict sent. -/
  conflict : Option (String × Node) := none
  trail : Array Undo := #[]
  /-- The trail, function-term and disequality sizes saved at each push. -/
  saved : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

namespace State

def getEqcInfo? (s : State) (n : Node) : Option EqcInfo := s.eqcInfo.get? ⟨n⟩

/-- Set the information of a class, on the trail. -/
def setEqcInfo (s : State) (n : Node) (e : EqcInfo) : State :=
  let old := s.eqcInfo.get? ⟨n⟩
  let m := s.eqcInfo
  let tr := s.trail
  let s := { s with eqcInfo := {}, trail := #[] }
  { s with eqcInfo := m.insert ⟨n⟩ e, trail := tr.push (.eqcInfo ⟨n⟩ old) }

/-- Mark a term preregistered, on the trail. -/
def addPrereg (s : State) (n : Node) : State :=
  let m := s.preregistered
  let tr := s.trail
  let s := { s with preregistered := {}, trail := #[] }
  { s with preregistered := m.insert ⟨n⟩, trail := tr.push (.prereg ⟨n⟩) }

/-- `setPendingConflict`: the first one only, on the trail. -/
def setPendingConflict (s : State) (id : String) (premises : Array Node) : State :=
  if s.pendingConflict.isSome then s else
  { s with pendingConflict := some (id, premises), trail := s.trail.push .pendingConflict }

def push (s : State) : State :=
  { s with saved := s.saved.push (s.trail.size, s.functionTerms.size, s.disequalities.size) }

/-- Undo back to the push of level `k`. -/
def popTo (s : State) (k : Nat) : State := Id.run do
  let some (tsize, fsize, dsize) := s.saved[k]? | return s
  let mut pre := s.preregistered
  let mut eqc := s.eqcInfo
  let mut pend := s.pendingConflict
  let trail := s.trail
  let s := { s with preregistered := {}, eqcInfo := {}, trail := #[] }
  for i in [0:trail.size - tsize] do
    match trail[trail.size - 1 - i]! with
    | .prereg k => pre := pre.erase k
    | .eqcInfo k old => eqc := match old with
      | some v => eqc.insert k v
      | none => eqc.erase k
    | .pendingConflict => pend := none
  return { s with preregistered := pre, eqcInfo := eqc, pendingConflict := pend, trail := trail.take tsize,
                  functionTerms := s.functionTerms.take fsize,
                  disequalities := s.disequalities.take dsize, saved := s.saved.take k }

end State

end Telos.Solver.Strings
