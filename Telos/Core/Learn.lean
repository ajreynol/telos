import Std.Data.HashMap
import Telos.Core.Node.Key

/-!
# Learned literals

The side condition of `SemProc.learn` (`Telos/Core/Semantic.lean`): the
conjunction `m` is the conjunction `n` with literals added, each learned by
Boolean propagation from the conjuncts of `n` (the circuit propagator of
non-clausal simplification, `Telos/Preprocess/CircuitPure.lean`).

The plan is the propagator's trace: each item gives a node a value, with a
reason, and is checked against the values of the earlier items (`Assign`):

* `root pos`: the node is the conjunct `pos` of `n`, and the value is `true`;
* `fwd s`: the three-valued value of the node's connective, from the values of
  its children, is the value (`eval3`);
* `bwd p`: the node is a child of the node of the item `p`, and giving it the
  other value would make that node's three-valued value the opposite of its own.

So in a model of `n`, every item holds (`verification/TelosProofs/Core/Learn.lean`).
For the values to be Booleans, the nodes must be well typed; the **skeleton**
shows it: a conjunct of `n`, or a child of an earlier skeleton node that is a
Boolean connective. Items with reason `fwd` give the skeleton node they are.

The check is linear in the size of the trace times the arity of the
connectives.
-/

namespace Telos

/-- Why a trace item's node has its value. -/
inductive LReason where
  | root (pos : Nat)
  | bwd (parent : Nat)
  | fwd (skel : Nat)
  deriving Inhabited

structure LItem where
  node : Node
  value : Bool
  reason : LReason
  deriving Inhabited

/-- A node shown well typed: the conjunct `pos` of `n` (`parent = none`), or
the child `pos` of the skeleton node `parent`. -/
structure SkelItem where
  node : Node
  parent : Option Nat
  pos : Nat

structure LearnPlan where
  skel : Array SkelItem
  trace : Array LItem
  /-- The trace items whose literals are the added conjuncts, in order. -/
  lits : Array Nat

/-- The Boolean connectives the propagator goes through. -/
def isBoolConn : Node → Bool
  | .app (.kind .AND) _ | .app (.kind .OR) _ | .app (.kind .NOT) _ | .app (.kind .ITE) _
  | .app (.kind .EQUAL) _ | .app (.kind .XOR) _ | .app (.kind .IMPLIES) _ => true
  | _ => false

/-- The values given so far. -/
abbrev Assign := Std.HashMap Key Bool

/-- The value of `c`: given, or a Boolean constant's. -/
def Assign.val (A : Assign) (c : Node) : Option Bool :=
  match c with
  | .const (.boolean b) => some b
  | c => A.get? ⟨c⟩

/-- The three-valued value of the connective `k` with children `cs`, from the
values of the children. -/
def eval3K (A : Assign) (k : Kind) (cs : Array Node) : Option Bool :=
  match k with
  | .AND =>
    if cs.any (fun c => A.val c == some false) then some false
    else if cs.all (fun c => A.val c == some true) then some true else none
  | .OR =>
    if cs.any (fun c => A.val c == some true) then some true
    else if cs.all (fun c => A.val c == some false) then some false else none
  | .NOT => if h : cs.size = 1 then (A.val cs[0]).map (!·) else none
  | .ITE =>
    if h : cs.size = 3 then
      match A.val cs[0] with
      | some true => A.val cs[1]
      | some false => A.val cs[2]
      | none =>
        match A.val cs[1], A.val cs[2] with
        | some a, some b => if a == b then some a else none
        | _, _ => none
    else none
  | .EQUAL =>
    if h : cs.size = 2 then
      if cs[0] == cs[1] then none else
      match A.val cs[0], A.val cs[1] with
      | some a, some b => some (a == b)
      | _, _ => none
    else none
  | .XOR =>
    if h : cs.size = 2 then
      if cs[0] == cs[1] then none else
      match A.val cs[0], A.val cs[1] with
      | some a, some b => some (a != b)
      | _, _ => none
    else none
  | .IMPLIES =>
    if h : cs.size = 2 then
      match A.val cs[0], A.val cs[1] with
      | some false, _ => some true
      | _, some true => some true
      | some true, some false => some false
      | _, _ => none
    else none
  | _ => none

/-- The three-valued value of a connective, from the values of its children. -/
def eval3 (A : Assign) : Node → Option Bool
  | .app (.kind k) cs => eval3K A k cs
  | _ => none

namespace LearnPlan

/-- The skeleton item `s` is a conjunct of `n` (children `cs`), or a child of an
earlier skeleton node that is a connective. -/
def skelOk (L : LearnPlan) (cs : Array Node) (s : Nat) : Bool :=
  match L.skel[s]? with
  | none => false
  | some it =>
    match it.parent with
    | none => cs[it.pos]? == some it.node
    | some p =>
      p < s && (L.skel[p]?.map fun P =>
        isBoolConn P.node && P.node.getChildren[it.pos]? == some it.node).getD false

/-- The trace item `idx` is justified by the values `A` of the earlier ones. -/
def itemOk (L : LearnPlan) (cs : Array Node) (A : Assign) (idx : Nat) (it : LItem) : Bool :=
  match it.reason with
  | .root pos => it.value && cs[pos]? == some it.node
  | .fwd s => (L.skel[s]?.map (·.node == it.node)).getD false && eval3 A it.node == some it.value
  | .bwd p =>
    p < idx && (L.trace[p]?.map fun P =>
      isBoolConn P.node && P.node.getChildren.contains it.node &&
        eval3 (A.insert ⟨it.node⟩ (!it.value)) P.node == some (!P.value)).getD false

/-- The values after the trace item `idx`, checked. -/
def replayStep (L : LearnPlan) (cs : Array Node) (A : Assign) (idx : Nat) : Option Assign :=
  match L.trace[idx]? with
  | some it => if L.itemOk cs A idx it then some (A.insert ⟨it.node⟩ it.value) else none
  | none => none

/-- The values of the trace, checked item by item. -/
def replay (L : LearnPlan) (cs : Array Node) : Option Assign :=
  (List.range L.trace.size).foldlM (L.replayStep cs) {}

/-- The literal of a trace item. -/
def litOf (it : LItem) : Node :=
  if it.value then it.node else .app (.kind .NOT) #[it.node]

/-- The side condition of `SemProc.learn`: `m` is `n` with the literals of
`lits` added, and the trace is justified. -/
def Ok (L : LearnPlan) (n m : Node) : Bool :=
  match n, m with
  | .app (.kind .AND) cs, .app (.kind .AND) ds =>
    2 ≤ cs.size && ds.size == cs.size + L.lits.size &&
      (List.range cs.size).all (fun i => ds[i]? == cs[i]?) &&
      (List.range L.lits.size).all (fun j =>
        match L.lits[j]? with
        | some t => t < L.trace.size && (L.trace[t]?.map fun it => ds[cs.size + j]? == some (litOf it)).getD false
        | none => false) &&
      (List.range L.skel.size).all (L.skelOk cs) &&
      (L.replay cs).isSome
  | _, _ => false

end LearnPlan

end Telos
