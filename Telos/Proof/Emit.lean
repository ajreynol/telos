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

/-- A proof step, with premises given by position in the proof. -/
structure Step where
  rule : CRule
  args : List Term
  premises : List Nat

abbrev EmitM := StateT (Array Step) (Except String)

/-- Add a step; return its position. -/
def push (s : Step) : EmitM Nat := do
  let steps ← get
  set (steps.push s)
  return steps.size

def argList : CArgList → List Term
  | .nil => []
  | .cons a as => a :: argList as

def indexList : CIndexList → List Int
  | .nil => []
  | .cons i is => i :: indexList is

/-- Append a command list that was checked from the empty state. Return the
position of its last fact. -/
def emitCmds (cs : CCmdList) : EmitM Nat := do
  let base := (← get).size
  let rec go : CCmdList → EmitM Unit
    | .nil => pure ()
    | .cons (.step r args prems) rest => do
      let h := (← get).size
      let prems ← (indexList prems).mapM fun (i : Int) => do
        if i < 0 || i ≥ ((h - base : Nat) : Int) then throw s!"premise {i} out of range"
        return h - 1 - i.toNat
      let _ ← push ⟨r, argList args, prems⟩
      go rest
    | .cons _ _ => throw "only `step` commands are supported in certificates"
  go cs
  let h := (← get).size
  if h == base then throw "empty certificate"
  return h - 1

/-- The fact `(= a b)` from a chain of facts `(= a a₁) (= a₁ a₂) … (= aₖ b)`:
`refl` for an empty chain, the fact itself for one, `trans` otherwise. -/
def closeChain (a : Node) (chain : Array Nat) : EmitM Nat :=
  match chain.toList with
  | [] => push ⟨.refl, [a.toEo], []⟩
  | [p] => pure p
  | ps => push ⟨.trans, [], ps⟩

/-- The congruence step for `n`, given the facts `(= cᵢ dᵢ)` for its children
(for a binder, the fact for its body). -/
def congStep (n : Node) (op : Op) (eqs : List Nat) : EmitM Nat :=
  match op.eoShape with
  | .rightAssocNil .. => push ⟨.nary_cong, [n.toEo], eqs⟩
  | _ => push ⟨.cong, [n.toEo], eqs⟩

/-- The positions of a chain of facts proving `(= n m)`. -/
partial def emitChain : {n m : Node} → Certified n m → EmitM (Array Nat)
  | _, _, .refl _ => pure #[]
  | _, _, .step cs _ rest => do
    let p ← emitCmds cs
    return #[p] ++ (← emitChain rest)
  | _, _, @Certified.congrArg op cs _ i _ hi _ _ hc rest => do
    let ch ← emitChain hc
    let mut eqs := #[]
    for h : j in [0:cs.size] do
      if j == i then eqs := eqs.push (← closeChain cs[i] ch)
      else eqs := eqs.push (← closeChain cs[j] #[])
    let p ← if ch.isEmpty then pure none
      else some <$> congStep (.app op cs) op eqs.toList
    return p.toArray ++ (← emitChain rest)
  | _, _, @Certified.congr op cs _ _ _ _ _ hc rest => do
    let chains ← (List.range cs.size).attach.mapM fun ⟨j, hj⟩ =>
      emitChain (hc j (List.mem_range.1 hj))
    let p ← if chains.all (·.isEmpty) then pure none
      else do
        let eqs ← (List.range cs.size).attach.mapM fun ⟨j, hj⟩ =>
          closeChain (cs[j]'(List.mem_range.1 hj)) chains[j]!
        some <$> congStep (.app op cs) op eqs
    return p.toArray ++ (← emitChain rest)
  | n, _, .arithNorm _ rest => do
    let p ← emitCmds (Certified.arithNormCmds n)
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
  let ((_ : Nat), steps) ← (do closeChain t (← emitChain r.2)).run #[]
  return steps

/-- The checker command for step `i`, whose premises are relative to it. -/
def Step.toCmd (i : Nat) (s : Step) : CCmd :=
  .step s.rule (toArgList s.args) (s.premises.foldr (fun p acc => .cons (Int.ofNat (i - 1 - p)) acc) .nil)

/-- Run the steps through Logos's checker from the empty state. Return the fact
each step proves; fail unless the last one is `goal`. -/
def checkProof (steps : Array Step) (goal : Term) : Except String (Array Term) := do
  let cmds := (steps.toList.zipIdx.map fun (s, i) => s.toCmd i).foldr .cons .nil
  if !decide (CmdListTranslationOk cmds) then
    throw "the proof does not meet Logos's translation side conditions"
  let mut S := CState.nil
  let mut facts := #[]
  for h : i in [0:steps.size] do
    let s := steps[i]
    S := __eo_invoke_cmd S (s.toCmd i)
    if let .Stuck := S then
      throw s!"step {i} ({ruleName s.rule}) is rejected by the checker"
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
    s!"(step {name i} {pr (p.facts[i]?.getD .Stuck)} :rule {ruleName st.rule}{prems}{args})"
  let goal := pr (eqFormula t s)
  let last := name (p.steps.size - 1)
  "\n".intercalate (decls ++ [s!"(assume @goal (not {goal}))"] ++ lines ++
    [s!"(step @false false :rule contra :premises ({last} @goal))"]) ++ "\n"

end Telos.Proof
