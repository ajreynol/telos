import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key

/-!
# The state of the theory of datatypes

The state of cvc5's `TheoryDatatypes` and its inference manager, as data. It is
a field of the central equality engine (`EqualityEngine.dt`), because the
theory reacts to the engine's notifications while the engine propagates
(`eqNotifyNewClass`, `eqNotifyMerge`), as cvc5's does.

cvc5's context-dependent parts (`CDO`, `CDHashMap`, `CDList` on the SAT
context) are undone on backtracking through a trail (`Undo`). The parts on the
user context (the purification skolems, the lemma cache) and the
non-context-dependent ones (the vectors of labels and selectors, whose
context-dependent sizes say how much of them is valid; the pending
inferences) are not.
-/

namespace Telos.Solver.DT

/-- `TheoryDatatypes::EqcInfo`: its fields are context dependent. -/
structure EqcInfo where
  /-- The class was instantiated (`d_inst`). -/
  inst : Bool := false
  /-- A constructor term of the class (`d_constructor`). -/
  constructor : Option Node := none
  /-- The class has selector applications (`d_selectors`). -/
  selectors : Bool := false
  deriving Inhabited

/-- A label (a tester asserted for a class): the tester literal, its argument,
and its constructor index. -/
structure Label where
  lit : Node
  arg : Node
  index : Nat
  deriving Inhabited

/-- A pending inference (`DatatypesInference`). -/
structure Inference where
  conc : Node
  /-- The explanation, `true` when there is none. -/
  exp : Node
  id : String
  deriving Inhabited

instance : Inhabited Key := ⟨⟨default⟩⟩

/-- A conflict of the theory, for its certificate: its inference, the literals
it explained, and, for a cycle, the constructor terms along it (each term, the
constructor term of its class, and the child position that continues the
cycle). -/
structure Conflict where
  id : String
  conf : Array Node
  cycle : Array (Node × Node × Nat) := #[]
  deriving Inhabited

/-- An entry of the trail. -/
inductive Undo where
  | eqcInfo (k : Key) (old : EqcInfo)
  | labels (k : Key) (old : Option Nat)
  | selApps (k : Key) (old : Option Nat)
  deriving Inhabited

structure State where
  /-- The theory is enabled. -/
  enabled : Bool := false
  /-- `d_eqc_info`: the object of a class persists, its fields are context
  dependent. -/
  eqcInfo : Std.HashMap Key EqcInfo := {}
  /-- `d_labels`: the number of valid labels of a class; a class has
  information exactly when it is here (`hasEqcInfo`). -/
  labels : Std.HashMap Key Nat := {}
  /-- `d_labels_data`, `d_labels_args`, `d_labels_tindex`. -/
  labelsData : Std.HashMap Key (Array Label) := {}
  /-- `d_selector_apps`: the number of valid selector applications. -/
  selApps : Std.HashMap Key Nat := {}
  /-- `d_selector_apps_data`. -/
  selAppsData : Std.HashMap Key (Array Node) := {}
  /-- `d_functionTerms`, for the care graph. -/
  functionTerms : Array Node := #[]
  /-- `d_term_sk`: the purification skolem of a constructor term (user
  context). -/
  termSk : Std.HashMap Key Node := {}
  /-- The inference manager's pending facts and lemmas, with whether a lemma is
  forced. -/
  pendingFacts : Array Inference := #[]
  pendingLemmas : Array Inference := #[]
  processingLemmas : Bool := false
  /-- `d_numCurrentFacts`, `d_numCurrentLemmas` since the last `reset`. -/
  sentFacts : Nat := 0
  sentLemmas : Nat := 0
  /-- A lemma was sent in this round of checks (`TheoryEngine::d_lemmasAdded`). -/
  lemmasAdded : Bool := false
  /-- `d_lemmasSent`, by rewritten lemma (user context). -/
  lemmaCache : Std.HashSet Key := {}
  /-- The internal facts asserted, with their inference and explanation, for the
  certificates (`EE.proveFact`). -/
  facts : Std.HashMap Key (String × Node) := {}
  /-- The last conflict of the theory. -/
  conflict : Option Conflict := none
  trail : Array Undo := #[]
  /-- The trail and function-term sizes saved at each push. -/
  saved : Array (Nat × Nat) := #[]
  deriving Inhabited

namespace State

def getEqcInfo (s : State) (n : Node) : EqcInfo := s.eqcInfo.getD ⟨n⟩ {}

-- Each update takes the map and the trail out of the state first, so that they
-- are updated in place rather than copied.

/-- Set the fields of the information of a class, on the trail. -/
def setEqcInfo (s : State) (n : Node) (e : EqcInfo) : State :=
  let old := s.getEqcInfo n
  let m := s.eqcInfo
  let tr := s.trail
  let s := { s with eqcInfo := {}, trail := #[] }
  { s with eqcInfo := m.insert ⟨n⟩ e, trail := tr.push (.eqcInfo ⟨n⟩ old) }

def setLabels (s : State) (n : Node) (v : Nat) : State :=
  let old := s.labels.get? ⟨n⟩
  let m := s.labels
  let tr := s.trail
  let s := { s with labels := {}, trail := #[] }
  { s with labels := m.insert ⟨n⟩ v, trail := tr.push (.labels ⟨n⟩ old) }

def setSelApps (s : State) (n : Node) (v : Nat) : State :=
  let old := s.selApps.get? ⟨n⟩
  let m := s.selApps
  let tr := s.trail
  let s := { s with selApps := {}, trail := #[] }
  { s with selApps := m.insert ⟨n⟩ v, trail := tr.push (.selApps ⟨n⟩ old) }

/-- Set entry `i` of the labels of `n` (reusing a spot, as cvc5 does). -/
def setLabelData (s : State) (n : Node) (i : Nat) (l : Label) : State :=
  let m := s.labelsData
  let s := { s with labelsData := {} }
  let a := m.getD ⟨n⟩ #[]
  let m := m.erase ⟨n⟩
  let a := if i < a.size then a.set! i l else a.push l
  { s with labelsData := m.insert ⟨n⟩ a }

def setSelAppData (s : State) (n : Node) (i : Nat) (t : Node) : State :=
  let m := s.selAppsData
  let s := { s with selAppsData := {} }
  let a := m.getD ⟨n⟩ #[]
  let m := m.erase ⟨n⟩
  let a := if i < a.size then a.set! i t else a.push t
  { s with selAppsData := m.insert ⟨n⟩ a }

def push (s : State) : State := { s with saved := s.saved.push (s.trail.size, s.functionTerms.size) }

/-- Undo back to the push of level `k`. -/
def popTo (s : State) (k : Nat) : State := Id.run do
  let some (tsize, fsize) := s.saved[k]? | return s
  let mut eqc := s.eqcInfo
  let mut labels := s.labels
  let mut selApps := s.selApps
  let trail := s.trail
  let s := { s with eqcInfo := {}, labels := {}, selApps := {}, trail := #[] }
  for i in [0:trail.size - tsize] do
    match trail[trail.size - 1 - i]! with
    | .eqcInfo k old => eqc := eqc.insert k old
    | .labels k old => labels := match old with
      | some v => labels.insert k v
      | none => labels.erase k
    | .selApps k old => selApps := match old with
      | some v => selApps.insert k v
      | none => selApps.erase k
  return { s with eqcInfo := eqc, labels, selApps, trail := trail.take tsize,
                  functionTerms := s.functionTerms.take fsize, saved := s.saved.take k }

end State

end Telos.Solver.DT
