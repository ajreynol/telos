import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Core.Node.ToEo
import Telos.Solver.EqualityEngine

/-!
# Models and their evaluation

A `sat` answer is certified by a model: a value for each free constant of the
input (a substitution), under which every input assertion evaluates to `true`
(`Model.satisfies`). The evaluation is telos's own (`Model.ev`), on nodes,
memoized, so that it is linear in the size of the input as a DAG.

Its theorem (`verification/TelosProofs/Solver/Model.lean`) relates it to
Logos's model semantics. The model of the substitution (`toSmtModel`) is well
formed, and evaluates each node as `Model.ev` does. So a model that satisfies
the input assertions makes them satisfiable. To make that correspondence
direct:
- the constants are keyed as Logos keys them: by the name of their Logos symbol
  (`keyName`), with their Logos type;
- function values carry their Logos types.

The values are those of the theories telos solves: Booleans, the elements of
uninterpreted sorts (numbered), and functions. A function is given by a finite
table (`FunTable`) with a default, curried as in Logos: a function of two
arguments maps the first to a function of one.

`buildModel` builds a model from the equality engine's classes of the relevant
terms, the subterms of the asserted literals, as cvc5's model builder does for
UF (`TheoryEngineModelBuilder`, from its model equality engine):
- each class of an uninterpreted sort is an element of its own;
- each relevant application gives an entry of its function's table;
- the definitions of the variables solved by preprocessing are evaluated last.

The builder is not trusted: `satisfies` checks its result.
-/

open Eo Smtm SmtEval

namespace Telos.Solver

/-- The Logos type of a type. -/
def tyS (T : TypeNode) : SmtType := __eo_to_smt_type T.toEo

/-- The name of the Logos symbol of the constant `x` (`native_uconst_id`). -/
def keyName (x : String) : native_String := native_uconst_id (constId x)

/-- A value of a model. -/
inductive MVal where
  | bool (b : Bool)
  /-- The `i`-th element of the uninterpreted sort `s` (Logos's `UValue`). -/
  | uval (s : Nat) (i : Nat)
  /-- The function of the table `fid` (`FunTable`), of Logos type `dom → rng`. -/
  | fn (fid : Nat) (dom rng : SmtType)
  deriving DecidableEq, Inhabited

/-- The Logos type of a value. -/
def MVal.ty : MVal → SmtType
  | .bool _ => .Bool
  | .uval s _ => .USort s
  | .fn _ d r => .FunType d r

/-- A function, as a table of its values, with a default. -/
structure FunTable where
  dom : SmtType
  rng : SmtType
  entries : List (MVal × MVal)
  default : MVal
  deriving Inhabited

structure Model where
  /-- The constants, by the name of their Logos symbol: their Logos type and
  their value. -/
  consts : Std.HashMap native_String (SmtType × MVal) := {}
  funs : Array FunTable := #[]
  deriving Inhabited

namespace Model

/-- The value of the constant `x` of type `T`. -/
def const (M : Model) (x : String) (T : TypeNode) : Option MVal :=
  match M.consts.get? (keyName x) with
  | some (T', v) => if T' == tyS T then some v else none
  | none => none

/-- Apply a function value to an argument. -/
def apply (M : Model) (f a : MVal) : Option MVal :=
  match f with
  | .fn fid dom rng =>
    match M.funs[fid]? with
    | some t =>
      if t.dom == dom && t.rng == rng then
        match t.entries.find? (·.1 == a) with
        | some (_, v) => some v
        | none => some t.default
      else none
    | none => none
  | _ => none

/-- Apply a function value to arguments, left to right. -/
def applyAll (M : Model) (f : MVal) : List MVal → Option MVal
  | [] => some f
  | a :: as => match M.apply f a with
    | some g => M.applyAll g as
    | none => none

/-- The tables are well typed: their entries and their defaults have the
table's range. -/
def tablesOk (M : Model) : Bool :=
  M.funs.all fun t => t.entries.all (fun (_, v) => v.ty == t.rng) && t.default.ty == t.rng

/-- Each constant has a value of its type. -/
def constsOk (M : Model) : Bool :=
  M.consts.toList.all fun (_, T, v) => v.ty == T

/-- The memo of the evaluation: the value of each node evaluated, if any. -/
abbrev Memo := Std.HashMap Key (Option MVal)

/-- The Boolean values of a list of values. -/
def bools : List MVal → Option (List Bool)
  | [] => some []
  | .bool b :: vs => (bools vs).map (b :: ·)
  | _ => none

/-- The value of a connective (or equality, or `ite`) of kind `k` on the values
`vs` of its children. -/
def combine (k : Kind) (vs : List MVal) : Option MVal :=
  match k, vs with
  | .NOT, [.bool b] => some (.bool !b)
  | .AND, vs => if 2 ≤ vs.length then (bools vs).map fun bs => .bool (bs.all id) else none
  | .OR, vs => if 2 ≤ vs.length then (bools vs).map fun bs => .bool (bs.any id) else none
  | .IMPLIES, [.bool a, .bool b] => some (.bool (!a || b))
  | .XOR, [.bool a, .bool b] => some (.bool (a != b))
  | .EQUAL, [a, b] => some (.bool (a == b))
  | .ITE, [.bool c, a, b] => some (if c then a else b)
  | _, _ => none

/-- The CPC list of the arguments of a `distinct` (as `Node.toEo` writes it). -/
def distinctList (cs : Array Node) : Term :=
  let xs := cs.toList.map Node.toEo
  eoRightAssocNil UserOp._at__at_TypedList_cons
    (typedNil UserOp._at__at_TypedList_cons (xs.headD Term.Stuck)) xs

/-- The arguments of a `distinct` have one type, as its Logos translation
requires (else it is not a Logos term). -/
def distinctTyped (cs : Array Node) : Bool :=
  __eo_to_smt_typed_list_elem_type (distinctList cs) != SmtType.None

/-- The values are pairwise distinct. -/
def distinctVals : List MVal → Bool
  | [] => true
  | v :: vs => vs.all (fun w => !(v == w)) && distinctVals vs

mutual
  /-- Evaluate a node, memoized (the memo is threaded, so it is updated in
  place); `none` outside the fragment evaluated (Booleans, equalities, `ite`,
  declared constants and their applications) or when the fuel runs out. -/
  def ev (M : Model) : Nat → Node → Memo → Option MVal × Memo
    | 0, _, S => (none, S)
    | n + 1, t, S =>
      match S.get? ⟨t⟩ with
      | some v => (v, S)
      | none =>
        match evNode M n t S with
        | (v, S) => (v, S.insert ⟨t⟩ v)
  termination_by n => (n, 0, 0)

  /-- Evaluate a node from its children. -/
  def evNode (M : Model) (n : Nat) (t : Node) (S : Memo) : Option MVal × Memo :=
    match t with
    | .const (.boolean b) => (some (.bool b), S)
    | .var x T => (M.const x T, S)
    | .app (.kind .DISTINCT) cs =>
      if distinctTyped cs then
        match evList M n cs.toList S with
        | (none, S) => (none, S)
        | (some vs, S) => (if 2 ≤ vs.length then some (.bool (distinctVals vs)) else none, S)
      else (none, S)
    | .app (.kind k) cs =>
      match evList M n cs.toList S with
      | (none, S) => (none, S)
      | (some vs, S) => (combine k vs, S)
    | .app (.node .APPLY_UF (.var f T)) cs =>
      match M.const f T with
      | none => (none, S)
      | some fv =>
        match evList M n cs.toList S with
        | (none, S) => (none, S)
        | (some vs, S) => (if vs.isEmpty then none else M.applyAll fv vs, S)
    | _ => (none, S)
  termination_by (n, 2, 0)

  /-- Evaluate a list of nodes. -/
  def evList (M : Model) (n : Nat) : List Node → Memo → Option (List MVal) × Memo
    | [], S => (some [], S)
    | c :: cs, S =>
      match ev M n c S with
      | (none, S) => (none, S)
      | (some v, S) =>
        match evList M n cs S with
        | (none, S) => (none, S)
        | (some vs, S) => (some (v :: vs), S)
  termination_by l => (n, 1, l.length)
end

/-- The fuel of the evaluation: a bound on the depth of the nodes. -/
def fuel : Nat := 1 <<< 20

/-- **The model satisfies the assertions**: its tables and constants are well
typed, and every assertion evaluates to `true`. -/
def satisfies (M : Model) (as : List Node) : Bool :=
  M.tablesOk && M.constsOk &&
    (match M.evList fuel as {} with
     | (some vs, _) => vs.all (· == .bool true)
     | (none, _) => false)

/-- Evaluate one node. -/
def eval (M : Model) (t : Node) : Option MVal := (M.ev fuel t {}).1

end Model

/-! ## Building a model -/

/-- The default value of a type, if it has one in the model. -/
def defaultValue : SmtType → Option MVal
  | .Bool => some (.bool false)
  | .USort s => some (.uval s 0)
  | _ => none

/-- The function and arguments of an application of a declared function. -/
def ufApp? : Node → Option (String × TypeNode × Array Node)
  | .app (.node .APPLY_UF (.var f T)) cs => some (f, T, cs)
  | _ => none

/-- The range of a Logos function type after `k` arguments. -/
def rangeAfter : SmtType → Nat → SmtType
  | .FunType _ r, k + 1 => rangeAfter r k
  | T, _ => T

structure Builder where
  model : Model := {}
  /-- The table of each function symbol and each prefix of argument values. -/
  tables : Std.HashMap (String × List Nat) Nat := {}
  /-- The values, by index, for the keys of `tables`. -/
  valIndex : Array MVal := #[]

/-- A new table of type `d → r` with no entries; its default is the default of
`r`, or, for a function type, a new table with no entries. -/
def newTable (d r : SmtType) : Nat → StateM Builder (Option Nat)
  | 0 => pure none
  | fuel + 1 => do
    let dflt ← match r with
      | .FunType d' r' => do
        match ← newTable d' r' fuel with
        | some sub => pure (some (MVal.fn sub d' r'))
        | none => pure none
      | _ => pure (defaultValue r)
    let some dflt := dflt | return none
    modifyGet fun b =>
      let fid := b.model.funs.size
      (some fid, { b with model := { b.model with funs := b.model.funs.push ⟨d, r, [], dflt⟩ } })

/-- The index of a value, for the keys of the tables. -/
def valueIndex (v : MVal) : StateM Builder Nat := do
  match (← get).valIndex.idxOf? v with
  | some i => return i
  | none => modifyGet fun b => (b.valIndex.size, { b with valIndex := b.valIndex.push v })

/-- The table of `f` (of Logos type `T`) after the arguments `pre`, created if
needed. -/
def tableOf (f : String) (T : SmtType) (pre : List MVal) : StateM Builder (Option Nat) := do
  let key ← pre.mapM valueIndex
  if let some fid := (← get).tables.get? (f, key) then return some fid
  let .FunType d r := rangeAfter T pre.length | return none
  let some fid ← newTable d r 64 | return none
  modify fun b => { b with tables := b.tables.insert (f, key) fid }
  return some fid

/-- Add an entry to a table, if it has none for the argument. -/
def addToTable (fid : Nat) (a v : MVal) : StateM Builder Unit := do
  let funs ← modifyGet fun b => (b.model.funs, { b with model := { b.model with funs := #[] } })
  let funs := funs.modify fid fun t =>
    if t.entries.any (·.1 == a) then t else { t with entries := t.entries ++ [(a, v)] }
  modify fun b => { b with model := { b.model with funs } }

/-- Record that `f` maps the arguments `args` to `v`. -/
def addEntry (f : String) (T : SmtType) (args : List MVal) (v : MVal) : StateM Builder Unit :=
  go [] args
where
  go (pre : List MVal) : List MVal → StateM Builder Unit
    | [] => pure ()
    | [a] => do
      let some fid ← tableOf f T pre | return
      addToTable fid a v
    | a :: rest => do
      let some fid ← tableOf f T pre | return
      let some sub ← tableOf f T (pre ++ [a]) | return
      let some t := (← get).model.funs[sub]? | return
      addToTable fid a (.fn sub t.dom t.rng)
      go (pre ++ [a]) rest

/-- The value of a class of the equality engine, given by its representative. -/
def classValue (ee : EE.EqualityEngine) (rep : Nat) : Option MVal :=
  let t := ee.nodes[rep]!
  match t with
  | .const (.boolean b) => some (.bool b)
  | _ => match t.typeHint with
    | some .boolean => some (.bool false)
    | some (.sort s) => some (.uval s (rep + 1))
    | _ => none

/-- Set the value of a constant. -/
def setConst (x : String) (T : TypeNode) (v : MVal) (b : Builder) : Builder :=
  { b with model := { b.model with consts := b.model.consts.insert (keyName x) (tyS T, v) } }

/-- The relevant terms (`Theory::computeRelevantTerms`): the subterms of the
asserted literals. Model construction considers only these, as cvc5's model
equality engine does. -/
partial def relevantTerms (asserted : Array Node) : Std.HashSet Key :=
  let rec go (n : Node) : StateM (Std.HashSet Key) Unit := do
    if (← get).contains ⟨n⟩ then return
    modify (·.insert ⟨n⟩)
    match n with
    | .app _ cs => for c in cs do go c
    | _ => pure ()
  ((asserted.forM go).run {}).2

/-- **Build a model** from the equality engine's classes of the relevant terms
`relevant`, for the free constants `syms` of the input, and the definitions
`defs` (`x := t`) of the variables solved by preprocessing, in order. -/
def buildModel (ee : EE.EqualityEngine) (relevant : Std.HashSet Key) (syms : List Node)
    (defs : List (Node × Node)) : Model := Id.run do
  let mut b : Builder := {}
  -- the constants and applications of the engine that are relevant
  for h : i in [0:ee.nodes.size] do
    if ee.isInternal[i]! then continue
    let t := ee.nodes[i]
    if !relevant.contains ⟨t⟩ then continue
    let some v := classValue ee (EE.find ee i) | continue
    match t with
    | .var x T => b := setConst x T v b
    | _ => match ufApp? t with
      | some (f, T, cs) =>
        let args := cs.toList.filterMap fun c =>
          (ee.nodeIds.get? ⟨c⟩).bind fun j => classValue ee (EE.find ee j)
        if args.length == cs.size then
          b := ((addEntry f (tyS T) args v).run b).2
      | none => pure ()
  -- the function symbols: their top table
  for f in syms do
    if let .var x T := f then
      if let .function _ _ := T then
        let (fid, b') := (tableOf x (tyS T) []).run b
        b := b'
        if let some fid := fid then
          let t := b.model.funs[fid]!
          b := setConst x T (.fn fid t.dom t.rng) b
  -- the other constants: the definitions, then the defaults
  for (x, t) in defs do
    if let .var name T := x then
      if let some v := b.model.eval t then b := setConst name T v b
  for x in syms do
    if let .var name T := x then
      if (b.model.const name T).isNone then
        if let some v := defaultValue (tyS T) then b := setConst name T v b
  return b.model

/-- The free constants of nodes. -/
partial def freeConsts (ns : List Node) : List Node :=
  let rec go (n : Node) : StateM (Std.HashSet Key × Array Node) Unit := do
    if (← get).1.contains ⟨n⟩ then return
    modify fun (s, a) => (s.insert ⟨n⟩, a)
    match n with
    | .var .. => modify fun (s, a) => (s, a.push n)
    | .app op cs => do
      if let .node _ f := op then go f
      for c in cs do go c
    | .skolem _ cs => for c in cs do go c
    | _ => pure ()
  ((ns.forM go).run ({}, #[])).2.2.toList

end Telos.Solver
