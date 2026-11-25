import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key

/-!
# The state of the theory of sets

The state of cvc5's `TheorySetsPrivate`, its `SolverState`, `TermRegistry` and
inference manager, as data (`src/theory/sets/`). Like the state of datatypes,
it is a field of the central equality engine (`EqualityEngine.sets`), because
the theory reacts to the engine's notifications while the engine propagates
(`eqNotifyNewClass`, `eqNotifyMerge`, `eqNotifyDisequal`).

The parts on the SAT context are undone on backtracking through a trail
(`Undo`):
- the singleton or empty set of a class (`EqcInfo::d_singleton`, a `CDO`; the
  objects themselves persist);
- the number of valid members of a class (`d_members`, a `CDHashMap`; the
  vectors `d_members_data` persist, and are overwritten past that number);
- the disequalities of sets (`d_deq`, a `CDHashMap` iterated in insertion
  order).

The parts on the user context (the processed disequalities, the proxies, the
lemma cache) are not undone, and the index of the current check (`Check`) is
rebuilt at each full-effort check (`SolverState::reset`).
-/

namespace Telos.Solver.Sets

/-- A pending lemma of the inference manager (`setupAndAddPendingLemma`). -/
structure Lemma where
  lem : Node
  id : String
  deriving Inhabited

/-- The index of the current full-effort check (`SolverState`'s maps, cleared
by `reset`). The maps keyed by nodes are `std::map`s in cvc5, iterated in the
order of node ids: they are kept here with their keys, and sorted where they
are iterated. -/
structure Check where
  /-- `d_set_eqc`: the classes of set type, in the engine's order. -/
  setEqc : Array Node := #[]
  /-- `d_eqc_emptyset`: the class of the empty set of each set type, by type. -/
  eqcEmptyset : Array (TypeNode × Node) := #[]
  /-- `d_eqc_singleton`: a singleton of a class. -/
  eqcSingleton : Std.HashMap Key Node := {}
  /-- `d_congruent`. -/
  congruent : Std.HashMap Key Node := {}
  /-- `d_nvar_sets`: the non-variable sets of a class, in order. -/
  nvarSets : Std.HashMap Key (Array Node) := {}
  /-- `d_var_set`: a variable of a class. -/
  varSet : Std.HashMap Key Node := {}
  /-- `d_pol_mems[0]`, `d_pol_mems[1]`: the positive and negative membership
  literals of a class, by the representative of the element. -/
  posMems : Std.HashMap Key (Array (Node × Node)) := {}
  negMems : Std.HashMap Key (Array (Node × Node)) := {}
  /-- `d_members_index`. -/
  membersIndex : Std.HashMap Key (Std.HashMap Key Node) := {}
  /-- `d_singleton_index`: a singleton by the representative of its element. -/
  singletonIndex : Std.HashMap Key Node := {}
  /-- `d_bop_index`: for each of union, intersection and minus (in that order,
  cvc5's `Kind` order), by the representatives of the arguments. -/
  bopIndex : Array (Kind × Array (Node × Array (Node × Node))) := #[]
  /-- `d_op_list`, the memberships, singletons and `set.choose`s (for the care
  graph). -/
  careTerms : Array Node := #[]
  deriving Inhabited

/-- An entry of the trail. -/
inductive Undo where
  | singleton (k : Key) (old : Option Node)
  | members (k : Key) (old : Option Nat)
  /-- An entry of `deq` was added (at the end). -/
  | deqAdd
  /-- Entry `i` of `deq` was deactivated. -/
  | deqOff (i : Nat)
  deriving Inhabited

structure State where
  /-- The theory is enabled. -/
  enabled : Bool := false
  /-- `d_eqc_info`: the classes with information (it persists). -/
  hasInfo : Std.HashSet Key := {}
  /-- `EqcInfo::d_singleton` (context dependent). -/
  singleton : Std.HashMap Key Node := {}
  /-- `d_members`: the number of valid members of a class (context dependent). -/
  members : Std.HashMap Key Nat := {}
  /-- `d_members_data`. -/
  membersData : Std.HashMap Key (Array Node) := {}
  /-- `d_deq`: the disequalities of sets, in insertion order, with whether they
  are active (context dependent). -/
  deq : Array (Node × Bool) := #[]
  deqIndex : Std.HashMap Key Nat := {}
  /-- `d_termProcessed` (user context). -/
  termProcessed : Std.HashSet Key := {}
  /-- `TermRegistry::d_proxy` (user context). -/
  proxy : Std.HashMap Key Node := {}
  /-- The index of the current check. -/
  check : Check := {}
  /-- The inference manager's pending lemmas (`InferenceManagerBuffered`). -/
  pendingLemmas : Array Lemma := #[]
  /-- `d_numCurrentFacts`, `d_numCurrentLemmas` since the last `reset`. -/
  sentFacts : Nat := 0
  sentLemmas : Nat := 0
  /-- `d_lemmasSent`, by rewritten lemma (user context). -/
  lemmaCache : Std.HashSet Key := {}
  /-- The internal facts asserted, with their inference and explanation, for the
  certificates. -/
  facts : Std.HashMap Key (String × Node) := {}
  /-- The last conflict of the theory: its inference, the conflict as sent, and
  its explanation (`TheoryEngine::getExplanation`). -/
  conflict : Option (String × Node × Array Node) := none
  trail : Array Undo := #[]
  /-- The trail and `deq` sizes saved at each push. -/
  saved : Array (Nat × Nat) := #[]
  deriving Inhabited

namespace State

-- Each update takes the map and the trail out of the state first, so that they
-- are updated in place rather than copied.

def setSingleton (s : State) (n : Node) (v : Option Node) : State :=
  let old := s.singleton.get? ⟨n⟩
  let m := s.singleton
  let tr := s.trail
  let s := { s with singleton := {}, trail := #[] }
  let m := match v with
    | some v => m.insert ⟨n⟩ v
    | none => m.erase ⟨n⟩
  { s with singleton := m, trail := tr.push (.singleton ⟨n⟩ old) }

def setMembers (s : State) (n : Node) (v : Nat) : State :=
  let old := s.members.get? ⟨n⟩
  let m := s.members
  let tr := s.trail
  let s := { s with members := {}, trail := #[] }
  { s with members := m.insert ⟨n⟩ v, trail := tr.push (.members ⟨n⟩ old) }

/-- Set entry `i` of the members of `n` (reusing a spot, as cvc5 does). -/
def setMemberData (s : State) (n : Node) (i : Nat) (atom : Node) : State :=
  let m := s.membersData
  let s := { s with membersData := {} }
  let a := m.getD ⟨n⟩ #[]
  let m := m.erase ⟨n⟩
  let a := if i < a.size then a.set! i atom else a.push atom
  { s with membersData := m.insert ⟨n⟩ a }

/-- The valid members of a class (`d_members_data` up to `d_members`). -/
def memberAtoms (s : State) (n : Node) : Array Node :=
  (s.membersData.getD ⟨n⟩ #[]).take (s.members.getD ⟨n⟩ 0)

/-- Add a disequality, active, unless it is there (`d_deq[eq] = true` when
absent). -/
def addDeq (s : State) (eq : Node) : State :=
  if s.deqIndex.contains ⟨eq⟩ then s else
  { s with deqIndex := s.deqIndex.insert ⟨eq⟩ s.deq.size, deq := s.deq.push (eq, true),
           trail := s.trail.push .deqAdd }

/-- Deactivate entry `i` of `deq`. -/
def deqOff (s : State) (i : Nat) : State :=
  if !(s.deq[i]?.map (·.2)).getD false then s else
  { s with deq := s.deq.modify i fun (e, _) => (e, false), trail := s.trail.push (.deqOff i) }

def push (s : State) : State := { s with saved := s.saved.push (s.trail.size, s.deq.size) }

/-- Undo back to the push of level `k`. -/
def popTo (s : State) (k : Nat) : State := Id.run do
  let some (tsize, _) := s.saved[k]? | return s
  let mut sing := s.singleton
  let mut mems := s.members
  let mut deq := s.deq
  let mut deqIndex := s.deqIndex
  let trail := s.trail
  let s := { s with singleton := {}, members := {}, deq := #[], deqIndex := {}, trail := #[] }
  for i in [0:trail.size - tsize] do
    match trail[trail.size - 1 - i]! with
    | .singleton k old => sing := match old with
      | some v => sing.insert k v
      | none => sing.erase k
    | .members k old => mems := match old with
      | some v => mems.insert k v
      | none => mems.erase k
    | .deqAdd =>
      if let some (e, _) := deq.back? then deqIndex := deqIndex.erase ⟨e⟩
      deq := deq.pop
    | .deqOff i => deq := deq.modify i fun (e, _) => (e, true)
  return { s with singleton := sing, members := mems, deq, deqIndex, trail := trail.take tsize,
                  saved := s.saved.take k }

end State

end Telos.Solver.Sets
