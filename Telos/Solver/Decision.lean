import Std.Data.HashMap
import Telos.Core.Node.Key
import Telos.Core.Node.FastType

/-!
# The justification decision heuristic

A port of cvc5's `JustificationStrategy` (`src/decision/`), with its assertion
lists (`AssertionList`), its cache of values (`JustifyCache`) and its stack
(`JustifyStack`, `JustifyInfo`). It walks the assertions (the input formulas
and the lemmas, split at the top level into conjuncts), and from the first
that is not yet true descends through its connectives to a theory atom with
no value, which it decides with the value that justifies the path
(`getNext`). It is done when every assertion is true (`isDone`).

In `stop-only` mode (cvc5's default for QF_LRA) it makes no decision: it only
stops the search once the assertions are justified, MiniSat deciding
otherwise.

Its context-dependent state (the indices of the lists, the cache, the stack,
the last decision) is restored at a pop of the SAT context (`push`, `pop`);
the list of assertions is user-context dependent, and never popped here. With
cvc5's defaults: no relevance order (`jh-rlv-order` is off), skolem
definitions first (`jh-skolem=FIRST`), when they become relevant
(`jh-skolem-rlv=ASSERT`).

The values of theory atoms come from the SAT solver, through an oracle that
the caller passes (`Oracle`).
-/

namespace Telos.Solver.Decision

/-- The mode (`--decision`). -/
inductive Mode where
  | internal | justification | stopOnly
  deriving BEq, Inhabited, Repr

/-- `expr::isTheoryAtom`: not a Boolean connective. -/
def isTheoryAtom : Node → Bool
  | .app (.kind k) cs =>
    !(k == .AND || k == .OR || k == .IMPLIES || k == .ITE || k == .XOR ||
      (k == .EQUAL && (cs[0]?.bind Node.typeHint) == some TypeNode.boolean))
  | _ => true

/-- The atom of a literal, and its polarity. -/
def atomOf : Node → Node × Bool
  | .app (.kind .NOT) #[a] => (a, false)
  | n => (n, true)

def isTheoryLiteral (n : Node) : Bool := isTheoryAtom (atomOf n).1

/-- A frame of the stack (`JustifyInfo`): a node to justify with a value, and
the index of its next child. -/
structure Info where
  node : Node
  desired : Bool
  child : Nat := 0
  deriving Inhabited

/-- What a push saves. -/
structure Mark where
  assertionIndex : Nat
  locals : Nat
  localIndex : Nat
  cacheLog : Nat
  current : Option Node
  infos : Array Info
  size : Nat
  lastDecision : Option Node
  deriving Inhabited

structure State where
  /-- The assertions (user-context dependent), and the next to visit. -/
  assertions : Array Node := #[]
  assertionIndex : Nat := 0
  /-- The local assertions: the skolem definitions that became relevant. -/
  locals : Array Node := #[]
  localIndex : Nat := 0
  /-- The values of the nodes justified so far (`JustifyCache`), and the order
  of their insertions (for a pop). -/
  cache : Std.HashMap Key Bool := {}
  cacheLog : Array Key := #[]
  /-- The stack: the assertion being justified, the frames, and how many of
  them are valid. -/
  current : Option Node := none
  infos : Array Info := #[]
  size : Nat := 0
  lastDecision : Option Node := none
  marks : Array Mark := #[]
  mode : Mode := .internal
  deriving Inhabited

/-- The SAT value of a theory atom, if it has one. -/
abbrev Oracle := Node → Option Bool

abbrev DecM := ReaderT Oracle (StateM State)

namespace State

def push (s : State) : State :=
  { s with marks := s.marks.push ⟨s.assertionIndex, s.locals.size, s.localIndex, s.cacheLog.size, s.current,
                                   s.infos, s.size, s.lastDecision⟩ }

def pop (s : State) : State := Id.run do
  let some m := s.marks.back? | return s
  let mut cache := s.cache
  for i in [m.cacheLog:s.cacheLog.size] do
    if let some k := s.cacheLog[i]? then cache := cache.erase k
  return { s with marks := s.marks.pop, assertionIndex := m.assertionIndex,
                  locals := s.locals.extract 0 m.locals, localIndex := m.localIndex,
                  cache, cacheLog := s.cacheLog.extract 0 m.cacheLog,
                  current := m.current, infos := m.infos, size := m.size, lastDecision := m.lastDecision }

/-- `presolve`. -/
def presolve (s : State) : State :=
  { s with lastDecision := none, assertionIndex := 0, localIndex := 0, current := none, size := 0 }

/-- `insertToAssertionList`: conjunctions (and negated disjunctions) split, theory
literals and constants left out. -/
def addAssertions (s : State) (lems : Array Node) (isLocal : Bool := false) : State := Id.run do
  let mut todo := lems.toList
  let mut out := #[]
  while true do
    match todo with
    | [] => break
    | curr :: rest =>
      todo := rest
      if curr == .const (.boolean true) || curr == .const (.boolean false) then continue
      let (atom, pol) := atomOf curr
      match atom with
      | .app (.kind .AND) cs =>
        if pol then todo := cs.toList ++ todo; continue
      | .app (.kind .OR) cs =>
        if !pol then todo := (cs.toList.map fun c => match c with
          | .app (.kind .NOT) #[a] => a
          | c => .app (.kind .NOT) #[c]) ++ todo; continue
      | _ => pure ()
      if !isTheoryAtom atom then out := out.push curr
  return if isLocal then { s with locals := s.locals ++ out } else { s with assertions := s.assertions ++ out }

end State

/-- `JustifyCache::lookupValue`. -/
def lookupValue (n : Node) : DecM (Option Bool) := do
  let (atom, pol) := atomOf n
  let fix := fun (v : Bool) => if pol then v else !v
  if let some v := (← get).cache.get? ⟨atom⟩ then return some (fix v)
  if isTheoryAtom atom then
    if let some v := (← read) atom then
      modify fun s => { s with cache := s.cache.insert ⟨atom⟩ v, cacheLog := s.cacheLog.push ⟨atom⟩ }
      return some (fix v)
  return none

def setValue (n : Node) (v : Bool) : DecM Unit :=
  modify fun s => { s with cache := s.cache.insert ⟨n⟩ v, cacheLog := s.cacheLog.push ⟨n⟩ }

/-! ## The stack -/

def pushToStack (n : Node) (desired : Bool) : DecM Unit :=
  modify fun s =>
    let info : Info := ⟨n, desired, 0⟩
    { s with infos := if s.size < s.infos.size then s.infos.set! s.size info else s.infos.push info,
             size := s.size + 1 }

def resetStack (n : Node) : DecM Unit := do
  modify fun s => { s with current := some n, size := 0 }
  pushToStack n true

def clearStack : DecM Unit := modify fun s => { s with current := none, size := 0 }

def popStack : DecM Unit := modify fun s => { s with size := s.size - 1 }

/-- The top frame, if any. -/
def getCurrent : DecM (Option Info) := do
  let s ← get
  return if s.size == 0 then none else some s.infos[s.size - 1]!

/-- `getNextChildIndex` of the top frame. -/
def nextChildIndex : DecM Nat := do
  let s ← get
  let i := s.infos[s.size - 1]!.child
  set { s with infos := s.infos.modify (s.size - 1) fun f => { f with child := i + 1 } }
  return i

/-! ## Assertions -/

/-- `AssertionList::getNextAssertion`. -/
def nextAssertion (isLocal : Bool) : DecM (Option Node) := do
  let s ← get
  if isLocal then
    if s.localIndex < s.locals.size then
      set { s with localIndex := s.localIndex + 1 }
      return some s.locals[s.localIndex]!
    return none
  if s.assertionIndex < s.assertions.size then
    set { s with assertionIndex := s.assertionIndex + 1 }
    return some s.assertions[s.assertionIndex]!
  return none

/-- `refreshCurrentAssertionFromList`: the next assertion not yet true. -/
def refreshFromList (isLocal : Bool) : DecM Bool := do
  let mut curr ← nextAssertion isLocal
  while true do
    let some c := curr | return false
    match ← lookupValue c with
    | some false =>
      resetStack c
      popStack
      modify fun s => { s with lastDecision := none }
      return true
    | none =>
      resetStack c
      modify fun s => { s with lastDecision := none }
      return true
    | some true => curr ← nextAssertion isLocal
  return false

/-- `refreshCurrentAssertion`: the skolem definitions first. -/
def refreshCurrentAssertion : DecM Bool := do
  if (← get).current.isSome then return true
  if ← refreshFromList true then return true
  refreshFromList false

/-! ## Justifying -/

/-- `getNextJustifyNode`: the next child of the top frame to justify, with its
desired value; or none when the frame has a value (cached), which then is
`lastChildVal`. -/
def getNextJustifyNode (ji : Info) (lastChildVal : Option Bool) : DecM (Option (Node × Bool) × Option Bool) := do
  let (curr, currPol) := atomOf ji.node
  let cs := match curr with
    | .app _ cs => cs
    | _ => #[]
  let mut i ← nextChildIndex
  let currDesired := if currPol then ji.desired else !ji.desired
  let mut value : Option Bool := none
  let mut desired : Option Bool := none
  match curr with
  | .app (.kind k) _ =>
    if k == .AND || k == .OR then
      if i == 0 then
        if (k == .AND) == (currDesired == false) then
          for c in cs do
            if (← lookupValue c) == some currDesired then
              value := some currDesired
              break
        desired := some currDesired
      else if (k == .AND && lastChildVal == some false) || (k == .OR && lastChildVal == some true) ||
          i == cs.size then
        value := lastChildVal
      else desired := some currDesired
    else if k == .IMPLIES then
      if i == 0 then
        if (← lookupValue cs[1]!) == some true then value := some true
        else desired := some !currDesired
      else if i == 1 then
        if lastChildVal == some false then value := some true
        else desired := some currDesired
      else value := lastChildVal
    else if k == .ITE then
      if i == 0 then
        let v1 ← lookupValue cs[1]!
        let v2 ← lookupValue cs[2]!
        if v1 == v2 then value := v1
        desired := some !(v1 == some !currDesired || v2 == some currDesired)
      else if i == 1 then
        if lastChildVal == some false then i ← nextChildIndex
        desired := some currDesired
      else value := lastChildVal
    else if k == .XOR || k == .EQUAL then
      if i == 0 then
        match ← lookupValue cs[1]! with
        | none => desired := some true
        | some v1 => desired := some (if (k == .EQUAL) == currDesired then v1 else !v1)
      else if i == 1 then
        let l := lastChildVal.getD true
        desired := some (if (k == .EQUAL) == currDesired then l else !l)
      else
        let v0 := (← lookupValue cs[0]!).getD true
        let l := lastChildVal.getD true
        value := some ((v0 == l) == (k == .EQUAL))
  | _ => pure ()
  if let some v := value then
    setValue curr v
    return (none, some (if currPol then v else !v))
  return (some (cs[i]!, desired.getD true), lastChildVal)

/-- `getNextInternal`: the next decision (a theory atom and its value), and
whether to stop the search (every assertion is justified). -/
def getNext : DecM (Option (Node × Bool) × Bool) := do
  if !(← refreshCurrentAssertion) then return (none, true)
  let mut lastChildVal : Option Bool := none
  if let some ld := (← get).lastDecision then
    lastChildVal ← lookupValue ld
    if lastChildVal.isNone then
      let curr := (← get).current.get!
      clearStack
      resetStack curr
  modify fun s => { s with lastDecision := none }
  repeat
    if (← getCurrent).isNone then return (none, false)
    let mut ji : Option Info := none
    let mut next : Option (Node × Bool) := none
    repeat
      ji ← getCurrent
      let some info := ji | break
      let (n, v) ← getNextJustifyNode info lastChildVal
      next := n
      lastChildVal := v
      if next.isNone then popStack else break
    match next with
    | none =>
      -- the assertion has a value
      if lastChildVal == some false then return (none, false)
      clearStack
      let _ ← refreshCurrentAssertion
      lastChildVal := none
    | some (n, desired) =>
      lastChildVal ← lookupValue n
      if lastChildVal.isNone then
        let (atom, pol) := atomOf n
        if isTheoryAtom atom then
          let v := if pol then desired else !desired
          modify fun s => { s with lastDecision := some n }
          if (← get).mode == .stopOnly then return (none, false)
          return (some (atom, v), false)
        else pushToStack n desired
    if (← get).current.isNone then break
  return (none, true)

/-- `isDone`. -/
def isDone : DecM Bool := do return !(← refreshCurrentAssertion)

end Telos.Solver.Decision
