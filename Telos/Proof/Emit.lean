import Telos.Rewriter.Certified
import Telos.Rules.RuleNames
import Telos.Proof.Eunoia

/-!
# CPC proofs of rewrites

A certified rewrite `Rw t` keeps the CPC command lists of its steps. `emitProof`
turns it into one CPC proof of `(= t s)`, where `s` is the result:

* each step's command list is appended as is (its premises are offsets from the
  top of the proof stack, so they still point at its own facts);
* consecutive steps are joined by `trans`;
* a rewrite below an operator becomes `cong` (or `nary_cong`, for
  `:right-assoc-nil` operators), with `refl` for the children that do not change.

The assembled proof is then run through Logos's checker, from the empty state,
and must prove `(= t s)` (`checkProof`). So telos only prints proofs that Logos
accepts. `render` prints it in Eunoia syntax, as a refutation of
`(not (= t s))`, which Ethos and the `logos` executable can check.

None of this is trusted, nor needed for `rewrite_correct`.
-/

open Eo

namespace Telos.Proof

/-- What a proof step does to the proof's stack of facts. -/
inductive StepKind where
  /-- A rule step: pushes its conclusion. -/
  | step
  /-- `assume-push`: pushes the assumption (the step's one argument). -/
  | assume
  /-- `step-pop`: pops the facts down to the last assumption, and pushes its
  conclusion, which may use it. -/
  | pop
  deriving DecidableEq, Inhabited

/-- A proof step, with premises given by position in the proof. -/
structure Step where
  rule : CRule
  args : List Term
  premises : List Nat
  kind : StepKind := .step
  deriving Inhabited

/-- The steps so far, and the positions of the facts on the stack. -/
structure EmitState where
  steps : Array Step := #[]
  stack : Array Nat := #[]

abbrev EmitM := StateT EmitState (Except String)

/-- Add a step; return its position. -/
def push (s : Step) : EmitM Nat := do
  let st ← get
  let i := st.steps.size
  let stack := match s.kind with
    | .pop =>
      -- drop the facts down to (and including) the last assumption
      match (st.stack.toList.reverse.findIdx? fun (j : Nat) => (st.steps[j]! : Step).kind == StepKind.assume) with
      | some k => st.stack.take (st.stack.size - 1 - k)
      | none => st.stack
    | _ => st.stack
  set { steps := st.steps.push s, stack := stack.push i : EmitState }
  return i

def argList : CArgList → List Term
  | .nil => []
  | .cons a as => a :: argList as

def indexList : CIndexList → List Int
  | .nil => []
  | .cons i is => i :: indexList is

/-- Append a command list that was checked from the empty state. Return the
position of its last fact. -/
def emitCmds (cs : CCmdList) : EmitM Nat := do
  let base := (← get).steps.size
  let baseStack := (← get).stack.size
  -- a premise `i` is the `i`-th fact from the top of the stack
  let resolve (prems : CIndexList) : EmitM (List Nat) := do
    let stack := (← get).stack
    (indexList prems).mapM fun (i : Int) => do
      if i < 0 || i ≥ ((stack.size - baseStack : Nat) : Int) then throw s!"premise {i} out of range"
      return stack[stack.size - 1 - i.toNat]!
  let rec go : CCmdList → EmitM Unit
    | .nil => pure ()
    | .cons (.step r args prems) rest => do
      let _ ← push ⟨r, argList args, ← resolve prems, .step⟩
      go rest
    | .cons (.assume_push F) rest => do
      let _ ← push ⟨.refl, [F], [], .assume⟩
      go rest
    | .cons (.step_pop r args prems) rest => do
      let _ ← push ⟨r, argList args, ← resolve prems, .pop⟩
      go rest
    | .cons _ _ => throw "only `step`, `assume-push` and `step-pop` commands are supported in certificates"
  go cs
  let h := (← get).steps.size
  if h == base then throw "empty certificate"
  return h - 1

/-- The fact `(= a b)` from a chain of facts `(= a a₁) (= a₁ a₂) … (= aₖ b)`:
`refl` for an empty chain, the fact itself for one, `trans` otherwise. -/
def closeChain (a : Node) (chain : Array Nat) : EmitM Nat :=
  match chain.toList with
  | [] => push ⟨.refl, [a.toEo], [], .step⟩
  | [p] => pure p
  | ps => push ⟨.trans, [], ps, .step⟩

/-- The congruence step for `n`, given the facts `(= cᵢ dᵢ)` for its children
(for a binder, the fact for its body). -/
def congStep (n : Node) (op : Op) (eqs : List Nat) : EmitM Nat :=
  match op.eoShape with
  | .rightAssocNil .. => push ⟨.nary_cong, [n.toEo], eqs, .step⟩
  | _ => push ⟨.cong, [n.toEo], eqs, .step⟩

/-- The positions of a chain of facts proving `(= n m)`. -/
partial def emitChain : {n m : Node} → Certified n m → EmitM (Array Nat)
  | _, _, .refl _ => pure #[]
  | _, _, .step cs _ rest => do
    let p ← emitCmds cs
    return #[p] ++ (← emitChain rest)
  | _, _, @Certified.congrArg op cs _ i _ hi _ _ hc rest => do
    let ch ← emitChain hc
    -- No step for a child that does not change (no `refl` facts either).
    if ch.isEmpty then return ← emitChain rest
    let mut eqs := #[]
    for h : j in [0:cs.size] do
      if j == i then eqs := eqs.push (← closeChain cs[i] ch)
      else eqs := eqs.push (← closeChain cs[j] #[])
    let p ← congStep (.app op cs) op eqs.toList
    return #[p] ++ (← emitChain rest)
  | _, _, @Certified.congr op cs _ _ _ _ _ hc rest => do
    let chains ← (List.range cs.size).attach.mapM fun ⟨j, hj⟩ =>
      emitChain (hc j (List.mem_range.1 hj))
    let p ← if chains.all (·.isEmpty) then pure none
      else do
        let eqs ← (List.range cs.size).attach.mapM fun ⟨j, hj⟩ =>
          closeChain (cs[j]'(List.mem_range.1 hj)) chains[j]!
        some <$> congStep (.app op cs) op eqs
    return p.toArray ++ (← emitChain rest)
  | n, _, @Certified.static _ k _ proc _ rest => do
    let p ← emitCmds (proc.cmds n k)
    return #[p] ++ (← emitChain rest)
  | _, _, @Certified.congrBody k vs body _ _ pats _ _ hc rest => do
    let ch ← emitChain hc
    let p ← if ch.isEmpty then pure none
      else do
        let e ← closeChain body ch
        some <$> congStep (.app (.kind k) ⟨vs :: body :: pats⟩) (.kind k) [e]
    return p.toArray ++ (← emitChain rest)

/-- The steps of a CPC proof of `(= t s)`, for the certified rewrite of `t` to `s`. -/
def emitProof {t : Node} (r : Rw t) : Except String (Array Step) := do
  let ((_ : Nat), st) ← (do closeChain t (← emitChain r.2)).run {}
  return st.steps

/-- The checker commands of the steps, with premises relative to the top of the
stack of facts, as the checker reads them. -/
def toCmds (steps : Array Step) : List CCmd := Id.run do
  -- `slot[j]` is the stack position of step `j`'s fact
  let mut slot : Array Nat := #[]
  let mut height : Nat := 0
  let mut cmds : Array CCmd := #[]
  for s in steps do
    let rel := fun (p : Nat) => Int.ofNat (height - 1 - slot[p]!)
    let prems := s.premises.foldr (fun p acc => .cons (rel p) acc) .nil
    match s.kind with
    | .step =>
      cmds := cmds.push (.step s.rule (toArgList s.args) prems)
      slot := slot.push height
      height := height + 1
    | .assume =>
      cmds := cmds.push (.assume_push (s.args.headD .Stuck))
      slot := slot.push height
      height := height + 1
    | .pop =>
      cmds := cmds.push (.step_pop s.rule (toArgList s.args) prems)
      -- the conclusion replaces the last assumption and the facts above it
      let k := ((List.range slot.size).reverse.find? fun j =>
        steps[j]!.kind == StepKind.assume && slot[j]! < height).getD 0
      let h := slot[k]!
      slot := slot.push h
      height := h + 1
  return cmds.toList

/-- The checker commands of the CPC proof of `(= t s)` for a certified rewrite
of `t` to `s`. Its last fact is `(= t s)`. -/
def cmdsOf {t : Node} (r : Rw t) : Option (List CCmd) :=
  match emitProof r with
  | .ok steps => some (toCmds steps)
  | .error _ => none

/-- A certified rewrite of `a` to `b`, from one of `b` to `a`: its proof, then
`symm`. -/
def reverse (a : Node) {b : Node} (r : Rw b) : Option (Rw a) :=
  if r.1 != a then none else
  let run : EmitM Nat := do
    let p ← closeChain b (← emitChain r.2)
    push ⟨.symm, [], [p], .step⟩
  match run.run {} with
  | .ok (_, st) => applyCmds ((toCmds st.steps).foldr .cons .nil) a
  | .error _ => none

/-- Run the steps through Logos's checker from the empty state. Return the fact
each step proves; fail unless the last one is `goal`. -/
def checkProof (steps : Array Step) (goal : Term) : Except String (Array Term) := do
  let cmdList := toCmds steps
  let cmds := cmdList.foldr .cons .nil
  if !decide (CmdListTranslationOk cmds) then
    throw "the proof does not meet Logos's translation side conditions"
  let mut S := CState.nil
  let mut facts := #[]
  for (c, i) in cmdList.zipIdx do
    S := __eo_invoke_cmd S c
    if let .Stuck := S then
      throw s!"step {i} ({ruleName ((steps[i]?.map (·.rule)).getD .refl)}) is rejected by the checker"
    facts := facts.push (__eo_state_proven_nth S 0)
  if facts.back? != some goal then throw "the proof does not prove the rewrite"
  return facts

/-- A checked CPC proof of `(= t s)`. -/
structure CheckedProof where
  steps : Array Step
  facts : Array Term

/-- The CPC proof of a certified rewrite, checked by Logos. -/
def proofOf {t : Node} (r : Rw t) : Except String CheckedProof := do
  let steps ← emitProof r
  let facts ← checkProof steps (eqFormula t r.1)
  return ⟨steps, facts⟩

/-- Print the proof as Eunoia commands: the given declarations, the assumption
`(not (= t s))`, the steps, and `false` by `contra`. -/
def CheckedProof.render (p : CheckedProof) (N : Eunoia.Names) (decls : List String)
    (t s : Node) : String :=
  let pr := Eunoia.print N
  let name (i : Nat) := s!"@p{i}"
  let lines := p.steps.toList.zipIdx.map fun (st, i) =>
    let prems := if st.premises.isEmpty then ""
      else s!" :premises ({" ".intercalate (st.premises.map name)})"
    let args := if st.args.isEmpty then "" else s!" :args ({" ".intercalate (st.args.map pr)})"
    match st.kind with
    | .assume => s!"(assume-push {name i} {pr (st.args.headD .Stuck)})"
    | .pop => s!"(step-pop {name i} {pr (p.facts[i]?.getD .Stuck)} :rule {ruleName st.rule}{prems}{args})"
    | .step => s!"(step {name i} {pr (p.facts[i]?.getD .Stuck)} :rule {ruleName st.rule}{prems}{args})"
  let goal := pr (eqFormula t s)
  let last := name (p.steps.size - 1)
  "\n".intercalate (decls ++ [s!"(assume @goal (not {goal}))"] ++ lines ++
    [s!"(step @false false :rule contra :premises ({last} @goal))"]) ++ "\n"

end Telos.Proof
