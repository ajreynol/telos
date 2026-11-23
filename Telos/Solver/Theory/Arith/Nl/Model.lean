import Telos.Solver.Theory.Arith.Nl.Basic

/-!
# The model of the nonlinear extension

A port of cvc5's `NlModel` (`src/theory/arith/nl/nl_model.cpp`). It starts
from the linear solver's model (`TheoryArithPrivate::collectModelValues`, on
the relevant terms), in which each monomial is a variable of its own, and
gives two values to each term:
- the **abstract** value: a term's own value in the linear model, if it has
  one (a monomial's included), else computed from its children's;
- the **concrete** value: computed from the children's values, so that a
  monomial is the product of its factors' values.

The extension refines where the two disagree. The model check (`checkModel`)
tries to repair the model instead: it solves equalities for a variable, fixes
every other variable to its value, and checks the assertions under the
substitution; the repaired values then override the linear model's
(`getModelValueRepair`).

Approximate bounds of variables (`d_check_model_bounds`) come only from
transcendental functions, which safe mode excludes, so there are none here:
the parts of `simpleCheckModelLit` that need them never apply.

Untrusted: a `sat` answer is certified by the model check of the engine
(`Telos/Solver/Model.lean`), which evaluates the input in the final model.
-/

namespace Telos.Solver.Arith.Nl

/-- The value of a constant node. -/
def valOf (n : Node) : Option Rat := constVal? n

/-- The node of a Boolean or arithmetic value of the type of `n`. -/
def mkVal (n : Node) (q : Rat) : Node := mkConstOf n q

/-- The value of an application to constants of a kind of arithmetic or the
Booleans, as the rewriter would compute it; `none` when it is not one we
evaluate (the caller rewrites instead). -/
def evalConst (n : Node) : Option Node :=
  match n with
  | .app (.kind k) cs =>
    let qs := cs.filterMap valOf
    let bs := cs.filterMap Node.getConstBoolean?
    let allQ := qs.size == cs.size
    let allB := bs.size == cs.size
    match k with
    | .ADD => if allQ then some (mkVal n (qs.foldl (· + ·) 0)) else none
    | .MULT => if allQ then some (mkVal n (qs.foldl (· * ·) 1)) else none
    | .SUB => if allQ && qs.size == 2 then some (mkVal n (qs[0]! - qs[1]!)) else none
    | .NEG => if allQ && qs.size == 1 then some (mkVal n (-qs[0]!)) else none
    | .TO_REAL => if allQ && qs.size == 1 then some (.const (.rational qs[0]!)) else none
    | .DIVISION =>
      if allQ && qs.size == 2 && qs[1]! != 0 then some (.const (.rational (qs[0]! / qs[1]!))) else none
    | .ABS => if allQ && qs.size == 1 then some (mkVal n (if qs[0]! < 0 then -qs[0]! else qs[0]!)) else none
    | .GEQ => if allQ && qs.size == 2 then some (Node.mkBool (qs[0]! ≥ qs[1]!)) else none
    | .GT => if allQ && qs.size == 2 then some (Node.mkBool (qs[0]! > qs[1]!)) else none
    | .LEQ => if allQ && qs.size == 2 then some (Node.mkBool (qs[0]! ≤ qs[1]!)) else none
    | .LT => if allQ && qs.size == 2 then some (Node.mkBool (qs[0]! < qs[1]!)) else none
    | .EQUAL =>
      if allQ && qs.size == 2 then some (Node.mkBool (qs[0]! == qs[1]!))
      else if allB && bs.size == 2 then some (Node.mkBool (bs[0]! == bs[1]!))
      else none
    | .NOT => if allB && bs.size == 1 then some (Node.mkBool (!bs[0]!)) else none
    | .AND => if allB then some (Node.mkBool (bs.all id)) else none
    | .OR => if allB then some (Node.mkBool (bs.any id)) else none
    | .IMPLIES => if allB && bs.size == 2 then some (Node.mkBool (!bs[0]! || bs[1]!)) else none
    | .XOR => if allB && bs.size == 2 then some (Node.mkBool (bs[0]! != bs[1]!)) else none
    | .ITE =>
      match cs[0]?.bind Node.getConstBoolean?, cs[1]?, cs[2]? with
      | some c, some t, some e => if (valOf t).isSome || (Node.getConstBoolean? t).isSome then
          some (if c then t else e) else none
      | _, _, _ => none
    | _ => none
  | _ => none

/-- `NlModel`. -/
structure NlModel where
  /-- `d_arithVal`: the linear model, extended with `0` for the terms that had
  no value (`getValueInternal`); in order of insertion. -/
  arithVal : Std.HashMap Key Node := {}
  arithKeys : Array Node := #[]
  concrete : Std.HashMap Key Node := {}
  abstract : Std.HashMap Key Node := {}
  usedApprox : Bool := false
  /-- `d_check_model_solved`: the equalities solved by the model check, and
  the variable each was solved for. -/
  solved : Std.HashMap Key Node := {}
  /-- `d_substitutions`. -/
  subs : ArithSubs := {}
  /-- The node order (for monomial sums and the rewriter). -/
  order : NodeOrder := {}
  deriving Inhabited

abbrev ModelM := StateM NlModel

namespace NlModel

/-- `reset`: the linear model. -/
def reset (o : NodeOrder) (vals : Array (Node × Node)) : NlModel :=
  vals.foldl (fun m (n, v) =>
    if m.arithVal.contains ⟨n⟩ then m
    else { m with arithVal := m.arithVal.insert ⟨n⟩ v, arithKeys := m.arithKeys.push n })
    { order := o }

/-- `resetCheck`. -/
def resetCheck (m : NlModel) : NlModel := { m with usedApprox := false, solved := {}, subs := {} }

def rw (t : Node) : ModelM Node := return Telos.rewrite t (← get).order

/-- `getValueInternal`: a leaf's linear value, or `0` (recorded). -/
def valueInternal (n : Node) : ModelM Node := do
  if n.isConst then return n
  if let some v := (← get).arithVal.get? ⟨n⟩ then return v
  let z := zeroOf n
  modify fun m => { m with arithVal := m.arithVal.insert ⟨n⟩ z, arithKeys := m.arithKeys.push n }
  return z

/-- `computeModelValue`. -/
partial def value (n : Node) (concrete : Bool) : ModelM Node := do
  let st ← get
  let cache : Std.HashMap Key Node := if concrete then st.concrete else st.abstract
  if let some v := cache.get? ⟨n⟩ then return v
  let ret ← do
    if n.isConst then pure n
    else if !concrete && (← get).arithVal.contains ⟨n⟩ then pure ((← get).arithVal.get? ⟨n⟩).get!
    else match n with
      | .app op cs =>
        if !traverses n then valueInternal n
        else
          let vs ← cs.mapM (value · concrete)
          let app : Node := .app op vs
          match evalConst app with
          | some v => pure v
          | none => rw app
      | _ => valueInternal n
  modify fun m => if concrete then { m with concrete := m.concrete.insert ⟨n⟩ ret }
    else { m with abstract := m.abstract.insert ⟨n⟩ ret }
  return ret

def concreteValue (n : Node) : ModelM Node := value n true
def abstractValue (n : Node) : ModelM Node := value n false

/-- `compareValue`: `-1`, `0` or `1`, of the values or of their absolute
values. -/
def compareValue (i j : Node) (absolute : Bool) : Int :=
  if i == j then 0 else
  let a := (valOf i).getD 0
  let b := (valOf j).getD 0
  if !absolute then (if a < b then -1 else 1)
  else
    let a := if a < 0 then -a else a
    let b := if b < 0 then -b else b
    if a == b then 0 else if a < b then -1 else 1

/-- `compare`. -/
def compare (i j : Node) (concrete absolute : Bool) : ModelM Int := do
  if i == j then return 0
  let ci ← value i concrete
  let cj ← value j concrete
  if ci.isConst then
    if cj.isConst then return compareValue ci cj absolute
    return 1
  return if cj.isConst then -1 else 0

/-! ## The model check -/

def hasAssignment (v : Node) : ModelM Bool := return (← get).subs.contains v

/-- `getSubstitutedForm`. -/
def substituted (s : Node) : ModelM Node := do
  let subs := (← get).subs
  if subs.isEmpty then return s
  rw (subs.apply s)

/-- `addSubstitution`: whether `v ↦ s` was added. -/
def addSubstitution (v s : Node) : ModelM Bool := do
  let subs := (← get).subs
  if let some cur := subs.get? v then
    if cur != s then return false
  if ArithSubs.hasArithSubterm (subs.apply s) v then return false
  let tmp : ArithSubs := ArithSubs.add {} v s
  let mut newSubs := subs.subs
  for i in [0:newSubs.size] do
    let ms := tmp.apply newSubs[i]!
    if ms != newSubs[i]! then newSubs := newSubs.set! i (← rw ms)
  modify fun m => { m with subs := { vars := m.subs.vars.push v, subs := newSubs.push s } }
  return true

/-- `solveEqualitySimple`. -/
partial def solveEqualitySimple (eq : Node) : ModelM Bool := do
  let mut seq := eq
  if !(← get).subs.isEmpty then
    seq ← substituted eq
    if let some b := seq.getConstBoolean? then
      if b then
        modify fun m => { m with solved := m.solved.insert ⟨eq⟩ Node.mkTrue }
        return true
      return false
  let o := (← get).order
  let some msum := MSum.getMonomialSumLit o seq | return false
  let mut valid := true
  let mut var : Option Node := none
  let mut b : Rat := 0
  let mut c : Rat := 0
  let mut uncVars : Array Node := #[]
  let mut uncFactors : Array Node := #[]
  let addU := fun (xs : Array Node) (x : Node) => if xs.contains x then xs else xs.push x
  for (k, coeff) in msum do
    let cv := MSum.coeffVal coeff
    match k with
    | none => c := cv
    | some v =>
      if isNlMult v then
        valid := false
        for f in v.getChildren do uncFactors := addU uncFactors f
      else if !v.isVar || (var.isSome && var != some v) then
        if valid then
          valid := false
          if b != 0 then
            if let some x := var then
              uncVars := addU uncVars x
              uncFactors := addU uncFactors x
        uncVars := addU uncVars v
        uncFactors := addU uncFactors v
      else
        b := cv
        var := some v
  if !valid then
    for uv in uncVars do
      if uv.isVar && !(← hasAssignment uv) then
        let (res, veqc, slv) := MSum.isolate uv msum .EQUAL
        if res != 0 then
          let slv ← rw slv
          if veqc.isNone && !ArithSubs.hasArithSubterm slv uv && slv.typeHint == uv.typeHint then
            let ret ← addSubstitution uv slv
            if ret then modify fun m => { m with solved := m.solved.insert ⟨eq⟩ uv }
            return ret
    for uvf in uncFactors do
      if uvf.isVar && !(← hasAssignment uvf) then
        let v ← concreteValue uvf
        if !v.isConst then return false
        let ret ← addSubstitution uvf v
        if ret then return ← solveEqualitySimple eq
        return false
    return false
  let some x := var | return false
  if isArithTerm x && !isRealTerm x then return false
  if b == 0 then return false
  let ret ← addSubstitution x (.const (.rational (-c / b)))
  if ret then modify fun m => { m with solved := m.solved.insert ⟨eq⟩ x }
  return ret

/-- `simpleCheckModelLit`, without approximate bounds (see the module
docstring): a literal that its substitution decides. -/
partial def simpleCheckLit (lit : Node) : ModelM Bool := do
  if let some b := lit.getConstBoolean? then return b
  let (pol, atom) := match lit with
    | .app (.kind .NOT) #[a] => (false, a)
    | a => (true, a)
  match atom with
  | .app (.kind .EQUAL) #[a, b] =>
    for (l, r) in [(a, b), (b, a)] do
      let lit2 := Node.mkNode .GEQ #[l, r]
      let lit2 ← rw (if pol then lit2 else Node.notNode lit2)
      let ok ← simpleCheckLit lit2
      if ok != pol then return ok
    return pol
  | .app (.kind .GEQ) _ =>
    let some msum := MSum.getMonomialSumLit (← get).order atom | return false
    -- (`simpleCheckModelMsum`: a variable without a bound fails)
    if msum.any (·.1.isSome) then return false
    let s : Rat := msum.foldl (fun (acc : Rat) (_, c) => acc + MSum.coeffVal c) 0
    return (s ≥ 0) == pol
  | _ => return false

/-- `NlModel::checkModel`: whether the substitution found satisfies the
assertions. -/
def checkModel (assertions : Array Node) : ModelM Bool := do
  for atom in assertions do
    if let .app (.kind .EQUAL) _ := atom then
      let _ ← solveEqualitySimple atom
  -- the other variables get their exact values
  let mut visited : Std.HashSet Key := {}
  for a in assertions do
    let mut visit := #[a]
    while !visit.isEmpty do
      let cur := visit.back!
      visit := visit.pop
      if visited.contains ⟨cur⟩ then continue
      visited := visited.insert ⟨cur⟩
      if isArithTerm cur && !cur.isConst then
        let isOp := match cur with
          | .app (.kind k) _ => k == .MULT || k == .ADD || k == .TO_REAL ||
              k == .POW2
          | _ => false
        if !isOp && !(← hasAssignment cur) then
          let v ← concreteValue cur
          if v.isConst then let _ ← addSubstitution cur v
      visit := visit ++ cur.getChildren
  let mut ok := true
  for a in assertions do
    if (← get).solved.contains ⟨a⟩ then continue
    let av ← substituted a
    if !(← simpleCheckLit av) then ok := false
  return ok

/-- `getModelValueRepair`: the linear model `vals` (as values), with the
values the model check fixed, and without the monomials' values. -/
def repair (vals : Array (Node × Rat)) : ModelM (Array (Node × Rat)) := do
  let m ← get
  let mut out : Array (Node × Rat) := vals
  if m.arithKeys.size > vals.size then
    out := m.arithKeys.filterMap fun n => (m.arithVal.get? ⟨n⟩).bind valOf |>.map (n, ·)
  for i in [0:m.subs.vars.size] do
    let v := m.subs.vars[i]!
    let s := m.subs.subs[i]!
    if let some q := valOf s then
      match out.findIdx? (·.1 == v) with
      | some j => out := out.set! j (v, q)
      | none => out := out.push (v, q)
  return out.filter fun (n, _) => !isNlMult n

end NlModel

end Telos.Solver.Arith.Nl
