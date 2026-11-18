import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Preprocess.SkolemSteps

/-!
# Reorganizing conjunctions in linear time

The pipeline is one conjunction, and splitting its conjuncts (`push_back`) or
adding conjuncts `true` for lemmas changes it as a whole. `aci_norm` proves
such steps, but Logos's program for it is cubic in the number of conjuncts (it
computes `eo::list_setof`, itself quadratic with deep term comparisons, at every
level of the right-nested list), which takes seconds on a few hundred
assertions.

`andReorg a b` proves `(= a b)` when every conjunct of each side is a conjunct
of the other, `true`, or a conjunction of such, by a CPC proof whose steps are
list walks without term comparisons:

1. `assume_push a`; `and_elim` its conjuncts (and those of nested conjunctions
   that `b` does not contain whole); `b` rebuilt by `and_intro` (`true` by
   `refl` and `true_elim`); `scope` gives `(=> a b)`. The same for `(=> b a)`.
2. With `E` the equality `(= a b)`: `implies_elim` of both implications,
   `cnf_equiv_neg1` and `cnf_equiv_neg2` (`(or E a b)` and
   `(or E (not a) (not b))`), resolution on `a` twice and `factoring`, giving
   `(or E (not b))` and `(or E b)`, then resolution on `b` and `factoring`: `E`.

It is checked by Logos's checker as any step is, so it needs no proof. It needs
`a` and `b` closed (`assume_push`); assertions are.
-/

namespace Telos.Preprocess

open Eo Node

/-- A hash of the top of a node, to depth `d`. The derived `Hashable Node`
hashes the whole tree, which on the pipeline's conjuncts dominates the cost. -/
def shallowHash : Nat → Node → UInt64
  | 0, _ => 7
  | _, .const c => hash c
  | _, .var n _ | _, .boundVar n _ => hash n
  | _, .skolem id _ => hash id
  | d + 1, .app op cs =>
    let h := mixHash (hash op.getKind) (hash cs.size)
    cs.attach.foldl (fun h ⟨c, _⟩ => mixHash h (shallowHash d c)) h

/-- A node keyed by its shallow hash; equality is still structural. -/
structure Key where
  node : Node

instance : BEq Key := ⟨fun a b => a.node == b.node⟩
instance : Hashable Key := ⟨fun k => shallowHash 3 k.node⟩

structure ReorgState where
  cmds : Array CCmd := #[]
  /-- The number of objects on the checker's state. -/
  depth : Nat := 0
  /-- The facts proven in the current scope: their positions on the state. -/
  facts : Std.HashMap Key Nat := {}

abbrev ReorgM := StateT ReorgState Option

/-- The premise index (counted from the top of the state) of position `pos`. -/
def ReorgM.rel (pos : Nat) : ReorgM Int := do
  return Int.ofNat ((← get).depth - 1 - pos)

/-- Emit `c`, which pushes one object; its position. -/
def ReorgM.emit (c : CCmd) : ReorgM Nat :=
  modifyGet fun s =>
    let cmds := s.cmds
    let d := s.depth
    let s := { s with cmds := #[] }
    (d, { s with cmds := cmds.push c, depth := d + 1 })

/-- The step `(r args)` from the facts at positions `prems`. -/
def ReorgM.stepAt (r : CRule) (args : List Term) (prems : List Nat) : ReorgM Nat := do
  let is ← prems.mapM ReorgM.rel
  ReorgM.emit (.step r (toArgList args) (is.foldr .cons .nil))

def ReorgM.record (n : Node) (pos : Nat) : ReorgM Unit :=
  modify fun s =>
    let fs := s.facts
    let s := { s with facts := {} }
    { s with facts := fs.insert ⟨n⟩ pos }

/-- Record the fact `n` at `pos`, and its conjuncts, by `and_elim`, if `n` is a
conjunction that is not to be kept whole. -/
partial def decompose (keep : Std.HashSet Key) (pos : Nat) (n : Node) : ReorgM Unit := do
  if (← get).facts.contains ⟨n⟩ then return
  ReorgM.record n pos
  if let .app (.kind .AND) cs := n then
    if !keep.contains ⟨n⟩ then
      for h : i in [0:cs.size] do
        let p ← ReorgM.stepAt .and_elim [.Numeral (Int.ofNat i)] [pos]
        decompose keep p cs[i]

/-- A proof of `t` from the recorded facts: a fact, `true`, or a conjunction of
such (`and_intro`). -/
partial def derive (t : Node) : ReorgM Nat := do
  if let some p := (← get).facts.get? ⟨t⟩ then return p
  let p ← match t with
    | .const (.boolean true) => do
      let p ← ReorgM.stepAt .refl [mkTrue.toEo] []
      ReorgM.stepAt .true_elim [] [p]
    | .app (.kind .AND) cs => do
      let ps ← cs.toList.mapM derive
      ReorgM.stepAt .and_intro [] ps
    | _ => failure
  ReorgM.record t p
  return p

/-- The conjuncts of `n`, as a set, and `n`. -/
def conjunctSet (n : Node) : Std.HashSet Key :=
  match n with
  | .app (.kind .AND) cs => cs.foldl (fun s c => s.insert ⟨c⟩) ({} : Std.HashSet Key) |>.insert ⟨n⟩
  | _ => ({} : Std.HashSet Key).insert ⟨n⟩

/-- `(=> a b)`, by `scope` over a proof of `b` from the assumption `a`
(translated, `ta`); its position. -/
def implication (a b : Node) (ta : Term) : ReorgM Nat := do
  let pa ← ReorgM.emit (.assume_push ta)
  decompose (conjunctSet b) pa a
  let pb ← derive b
  let i ← ReorgM.rel pb
  -- `step_pop` replaces the assumption and the facts above it
  modify fun s =>
    let cmds := s.cmds
    let s := { s with cmds := #[], facts := {} }
    { s with cmds := cmds.push (.step_pop .scope .nil (.cons i .nil)), depth := pa + 1 }
  return pa

/-- The commands of the proof of `(= a b)` described above. -/
def andReorgCmds (a b : Node) : Option (List CCmd) :=
  -- the translations of the (large) conjunctions, computed once
  let ta := a.toEo
  let tb := b.toEo
  let run : ReorgM Unit := do
    let i₁ ← implication a b ta
    let i₂ ← implication b a tb
    let c₄ ← ReorgM.stepAt .implies_elim [] [i₁]
    let c₂ ← ReorgM.stepAt .implies_elim [] [i₂]
    let e := eoApp2 UserOp.eq ta tb
    let c₁ ← ReorgM.stepAt .cnf_equiv_neg2 [e] []
    let c₃ ← ReorgM.stepAt .cnf_equiv_neg1 [e] []
    -- `(or E (not b) (not b))`, then `(or E (not b))`
    let r₁ ← ReorgM.stepAt .resolution [.Boolean false, ta] [c₁, c₂]
    let f₁ ← ReorgM.stepAt .factoring [] [r₁]
    -- `(or E b b)`, then `(or E b)`
    let r₂ ← ReorgM.stepAt .resolution [.Boolean true, ta] [c₃, c₄]
    let f₂ ← ReorgM.stepAt .factoring [] [r₂]
    -- `(or E E)`, then `E`
    let r₃ ← ReorgM.stepAt .resolution [.Boolean false, tb] [f₁, f₂]
    let _ ← ReorgM.stepAt .factoring [] [r₃]
  (run.run {}).map (·.2.cmds.toList)

/-- `a` rewritten to `b`, conjunctions with the same conjuncts up to nesting and
`true`, by the proof above. -/
def andReorg (a b : Node) : Option (Rw a) := do
  applyCmds (cmdList (← andReorgCmds a b)) a

end Telos.Preprocess
