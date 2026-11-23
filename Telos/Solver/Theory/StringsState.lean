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

/-- How the length of a term is registered (`LengthStatus`). -/
inductive LengthStatus where
  | split
  | geqOne
  | one
  | ignore
  deriving DecidableEq, Inhabited

/-- A pending lemma or fact of the inference manager (`InferInfo`, sent as a
lemma or asserted as a fact). -/
structure Inference where
  id : String
  conc : Node
  /-- The premises (`d_premises`). -/
  exp : Array Node := #[]
  /-- The part of the premises that is not explained by the equality engine
  (`d_noExplain`). -/
  noExplain : Array Node := #[]
  /-- `d_idRev`. -/
  idRev : Bool := false
  /-- The skolems to register when the lemma is sent (`d_skolems`). -/
  skolems : Array (Node × LengthStatus) := #[]
  /-- The phases to prefer when the lemma is sent (`d_pendingPhase`). -/
  phases : Array (Node × Bool) := #[]
  /-- The normal forms to record as a pair (`d_nfPair`). -/
  nfPair : Option (Node × Node) := none
  deriving Inhabited

/-- The base solver's information of a class (`BaseEqcInfo`). -/
structure BaseEqcInfo where
  bestContent : Option Node := none
  bestScore : Nat := 0
  base : Option Node := none
  exp : Option Node := none
  deriving Inhabited

/-- A normal form (`NormalForm`): the components `nf` of the term `base`,
explained by `exp`, each literal relevant from index `expDep.1` (forwards) and
`expDep.2` (backwards). -/
structure NormalForm where
  base : Node
  nf : Array Node := #[]
  isRev : Bool := false
  exp : Array Node := #[]
  expDep : Std.HashMap Key (Nat × Nat) := {}
  deriving Inhabited

/-- A possible inference of the core solver (`CoreInferInfo`). -/
structure CoreInferInfo where
  infer : Inference
  index : Nat := 0
  rev : Bool := false
  deriving Inhabited

/-- The data of a full-effort check, computed afresh by each (the base and core
solvers' maps). -/
structure Check where
  /-- `BaseSolver::d_eqcInfo`. -/
  baseInfo : Std.HashMap Key BaseEqcInfo := {}
  /-- `d_termIndex`: the signature (the operator applied to the
  representatives of the arguments, without the empty ones of a
  concatenation) of each term indexed, and its term. -/
  termIndex : Std.HashMap Key Node := {}
  /-- The trie of concatenations: the children of each prefix (as a
  signature), in order of insertion. -/
  concatChildren : Std.HashMap Key (Array Node) := {}
  /-- `d_stringLikeEqc`. -/
  stringLikeEqc : Array Node := #[]
  /-- `d_flat_form`, `d_flat_form_index`. -/
  flatForm : Std.HashMap Key (Array Node) := {}
  flatFormIndex : Std.HashMap Key (Array Nat) := {}
  /-- `d_eqc`: the concatenations of each class. -/
  eqcConcats : Std.HashMap Key (Array Node) := {}
  /-- `d_strings_eqc`, in an acyclic order. -/
  stringsEqc : Array Node := #[]
  /-- `d_normal_form`. -/
  normalForms : Std.HashMap Key NormalForm := {}
  /-- `d_pinfers`. -/
  pinfers : Array CoreInferInfo := #[]
  /-- `d_modelUnsoundId` is set. -/
  modelUnsound : Bool := false
  /-- `d_rlvDeq`. -/
  rlvDeq : Array Node := #[]
  /-- The relevant terms (`getRelevantTermSet`). -/
  relevant : Std.HashSet Key := {}
  deriving Inhabited

/-- An entry of the trail. -/
inductive Undo where
  | prereg (k : Key)
  | eqcInfo (k : Key) (old : Option EqcInfo)
  | pendingConflict
  | congruent (k : Key)
  | nfPair (k : Key) (old : Option (Array Node))
  /-- An extended term registered (`ExtTheory::registerTerm`). -/
  | extTerm (k : Key)
  /-- An extended term marked inactive (`markInactive`), with its old mark. -/
  | extActive (k : Key) (old : Bool)
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
  /-- The inference manager's pending facts and lemmas, and phases
  (`d_pendingReqPhase`). -/
  pendingFacts : Array Inference := #[]
  pendingLemmas : Array Inference := #[]
  pendingPhases : Array (Node × Bool) := #[]
  /-- `BaseSolver::d_congruent` (context dependent). -/
  congruent : Std.HashSet Key := {}
  /-- `CoreSolver::d_nfPairs` (context dependent). -/
  nfPairs : Std.HashMap Key (Array Node) := {}
  /-- The data of the current full-effort check. -/
  chk : Check := {}
  /-- A step was incomplete (`setModelUnsound`) in the last full-effort check:
  a `sat` answer is not justified. -/
  incomplete : Bool := false
  /-- The last full-effort check left a negative membership unprocessed
  (`STRINGS_RE_UNFOLD_NEG`, at last call, is not ported): a `sat` answer rests
  on the model check. -/
  negMemUnchecked : Bool := false
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
  /-- The last conflict of the theory: its inference, the conflict sent, and
  its premises before their explanation (for the certificate). -/
  conflict : Option (String × Node × Array Node) := none
  /-- `ExtTheory::d_ext_func_terms` (context dependent): the extended terms
  registered, in order, and whether each is active. -/
  extTerms : Array Node := #[]
  extActive : Std.HashMap Key Bool := {}
  /-- `ExtTheory::d_ci_inactive` (user context): the terms inactive
  independently of the SAT context. -/
  ciInactive : Std.HashSet Key := {}
  /-- `ExtfSolver::d_reduced` (user context): the memberships unfolded. -/
  reduced : Std.HashSet Key := {}
  /-- `TermRegistry::d_hasStrCode`: a `str.to_code` was preregistered. -/
  hasStrCode : Bool := false
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

/-- Mark a term congruent, on the trail. -/
def addCongruent (s : State) (n : Node) : State :=
  if s.congruent.contains ⟨n⟩ then s else
  let m := s.congruent
  let tr := s.trail
  let s := { s with congruent := {}, trail := #[] }
  { s with congruent := m.insert ⟨n⟩, trail := tr.push (.congruent ⟨n⟩) }

/-- Set the normal form pairs of a term, on the trail. -/
def setNfPairs (s : State) (n : Node) (v : Array Node) : State :=
  let old := s.nfPairs.get? ⟨n⟩
  let m := s.nfPairs
  let tr := s.trail
  let s := { s with nfPairs := {}, trail := #[] }
  { s with nfPairs := m.insert ⟨n⟩ v, trail := tr.push (.nfPair ⟨n⟩ old) }

/-- `ExtTheory::registerTerm`: an extended term, active, on the trail. -/
def registerExt (s : State) (n : Node) : State :=
  if s.extActive.contains ⟨n⟩ then s else
  let m := s.extActive
  let ts := s.extTerms
  let tr := s.trail
  let s := { s with extActive := {}, extTerms := #[], trail := #[] }
  { s with extActive := m.insert ⟨n⟩ true, extTerms := ts.push n, trail := tr.push (.extTerm ⟨n⟩) }

/-- `ExtTheory::markInactive`: in the SAT context (`satDep`), or also in the
user context. -/
def markInactive (s : State) (n : Node) (satDep : Bool := true) : State :=
  let s := s.registerExt n
  let old := (s.extActive.get? ⟨n⟩).getD true
  let m := s.extActive
  let tr := s.trail
  let s := { s with extActive := {}, trail := #[] }
  let s := { s with extActive := m.insert ⟨n⟩ false, trail := tr.push (.extActive ⟨n⟩ old) }
  if satDep then s else { s with ciInactive := s.ciInactive.insert ⟨n⟩ }

/-- `ExtTheory::isActive`. -/
def isActiveExt (s : State) (n : Node) : Bool :=
  (s.extActive.get? ⟨n⟩).getD false && !s.ciInactive.contains ⟨n⟩

/-- `ExtTheory::getActive`, of kind `k` if given. -/
def activeExt (s : State) (k : Option Kind := none) : Array Node :=
  s.extTerms.filter fun n => (k.isNone || some n.getKind == k) && s.isActiveExt n

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
  let mut cong := s.congruent
  let mut nfp := s.nfPairs
  let mut ext := s.extActive
  let mut exts := s.extTerms
  let trail := s.trail
  let s := { s with preregistered := {}, eqcInfo := {}, trail := #[], congruent := {}, nfPairs := {},
                    extActive := {}, extTerms := #[] }
  for i in [0:trail.size - tsize] do
    match trail[trail.size - 1 - i]! with
    | .prereg k => pre := pre.erase k
    | .eqcInfo k old => eqc := match old with
      | some v => eqc.insert k v
      | none => eqc.erase k
    | .pendingConflict => pend := none
    | .congruent k => cong := cong.erase k
    | .nfPair k old => nfp := match old with
      | some v => nfp.insert k v
      | none => nfp.erase k
    | .extTerm k =>
      ext := ext.erase k
      exts := exts.pop
    | .extActive k old => ext := ext.insert k old
  return { s with preregistered := pre, eqcInfo := eqc, pendingConflict := pend, trail := trail.take tsize,
                  congruent := cong, nfPairs := nfp, extActive := ext, extTerms := exts,
                  functionTerms := s.functionTerms.take fsize,
                  disequalities := s.disequalities.take dsize, saved := s.saved.take k }

end State

end Telos.Solver.Strings
