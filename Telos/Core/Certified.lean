import Telos.Core.Node.OfEo
import Telos.Core.Node.DecEq
import Cpc.TranslationChecks
import Telos.Core.FastTranslation
import Telos.Core.RuleNames
import Telos.Core.Profile
import Telos.Core.Static
import Telos.Core.Semantic
import Telos.Core.Tri

/-!
# Certified rewrite steps

Every rewrite telos performs is justified by CPC. A step from `n` to `m` is a
CPC command list `cs` that Logos's checker, run from the empty state, accepts,
and whose last proven fact is `(= n m)` (`ProvesEq`). `Certified n m` chains such
steps.

The certificate is checked by running Logos's own checker
(`__eo_invoke_cmd_list`), which Logos proves sound for every CPC rule. So
`Certified n m` implies that `n` and `m` are equivalent
(`Certified.equiv`, `verification/TelosProofs/Core/Certified.lean`), with no proof per
rule. Code that produces certified results, such as the theory rewriters, needs
no proof at all.

Only steps are run, never assumptions, so facts with free variables (for example
the body of a quantifier) can be proven.
-/

open Eo

namespace Telos

/-- The checker state after running `cs` from the empty state. -/
def runFromEmpty (cs : CCmdList) : CState :=
  __eo_invoke_cmd_list CState.nil cs

/-- `cs` proves `(= n m)`: it meets Logos's translation side conditions, its run
from the empty state is closed (not stuck, no open `assume_push`), and the last
fact proven is `(= n m)`. These are the hypotheses of Logos's
`proven_from_empty_valid`. -/
def ProvesEq (cs : CCmdList) (n m : Node) : Prop :=
  CmdListTranslationOk cs ∧ __eo_state_is_closed (runFromEmpty cs) = true ∧
    __eo_state_proven_nth (runFromEmpty cs) 0 = eqFormula n m

instance (cs : CCmdList) (n m : Node) : Decidable (ProvesEq cs n m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `n` rewrites to `m` by a chain of CPC-checked steps, at the top or below an
operator. It is data, not a proposition: it keeps the command lists, so that a
rewrite can be printed as a CPC proof (`Telos/Core/Proof/`). Its proof fields are
erased at run time. -/
inductive Certified : Node → Node → Type
  | refl (n : Node) : Certified n n
  /-- A CPC-checked step at the top. -/
  | step {n k m : Node} (cs : CCmdList) : ProvesEq cs n k → Certified k m → Certified n m
  /-- A rewrite of the child `i` of an application whose operator is congruent
  in its children (`Node.Equiv.congr`), all of which are well typed. -/
  | congrArg {op : Op} {cs : Array Node} {m : Node} (i : Nat) (c' : Node) (hi : i < cs.size) :
      op.eoShape.isChildCongruent = true →
      (op.childrenTypedOfParent = true ∨ ∀ c ∈ cs.toList, c.WellTyped) →
      Certified cs[i] c' → Certified (.app op (cs.set i c')) m → Certified (.app op cs) m
  /-- A rewrite of every child of such an application. -/
  | congr {op : Op} {cs ds : Array Node} {m : Node} (hsize : cs.size = ds.size) :
      op.eoShape.isChildCongruent = true →
      (op.childrenTypedOfParent = true ∨ ∀ c ∈ cs.toList, c.WellTyped) →
      ((i : Nat) → (hi : i < cs.size) → Certified cs[i] (ds[i]'(hsize ▸ hi))) →
      Certified (.app op ds) m → Certified (.app op cs) m
  /-- A statically justified step: `p.Ok n k` holds, and the CPC commands
  `p.cmds n k` are accepted by Logos's checker by a theorem
  (`StaticProc.provesEq`), so they are not run (`Telos/Core/Static.lean`). -/
  | static {n k m : Node} (p : StaticProc) : p.Ok n k → Certified k m → Certified n m
  /-- A semantically justified step: `p.Ok n k` holds, which implies that `n`
  and `k` are equivalent by a theorem (`SemProc.equiv`,
  `Telos/Core/Semantic.lean`); no CPC proof is run, nor printed. -/
  | semantic {n k m : Node} (p : SemProc) : p.Ok n k → Certified k m → Certified n m
  /-- A triangular substitution step on a conjunction (`Telos/Core/Tri.lean`):
  `P.Ok n k` holds, with the certified rewrites its chains use. -/
  | tri {n k m : Node} (P : TriPlan) : P.Ok n k = true →
      ((r : Nat) → (hr : r < P.rws.size) → Certified P.rws[r].1 P.rws[r].2) →
      Certified k m → Certified n m
  /-- A rewrite of the well-typed body of a quantifier
  (`Node.Equiv.congr_binder`). -/
  | congrBody {k : Kind} {vs body body' m : Node} {pats : List Node} :
      k.isQuantifier = true → body.WellTyped → Certified body body' →
      Certified (.app (.kind k) ⟨vs :: body' :: pats⟩) m →
      Certified (.app (.kind k) ⟨vs :: body :: pats⟩) m

def Certified.trans {a b c : Node} : Certified a b → Certified b c → Certified a c
  | .refl _, h₂ => h₂
  | .step cs h r, h₂ => .step cs h (r.trans h₂)
  | .congrArg i c' hi hop hwt hc r, h₂ => .congrArg i c' hi hop hwt hc (r.trans h₂)
  | .congr hsize hop hwt hc r, h₂ => .congr hsize hop hwt hc (r.trans h₂)
  | .congrBody hk hb hc r, h₂ => .congrBody hk hb hc (r.trans h₂)
  | .static p h r, h₂ => .static p h (r.trans h₂)
  | .semantic p h r, h₂ => .semantic p h (r.trans h₂)
  | .tri P h rws r, h₂ => .tri P h rws (r.trans h₂)

/-- A certified rewrite of `n`: the result, and how it was obtained. -/
abbrev Rw (n : Node) := (m : Node) × Certified n m

namespace Rw

/-- No rewrite. -/
def id (n : Node) : Rw n := ⟨n, .refl n⟩

instance (n : Node) : Inhabited (Rw n) := ⟨id n⟩

/-- `r` followed by `s`. -/
def trans {n : Node} (r : Rw n) (s : Rw r.1) : Rw n := ⟨s.1, r.2.trans s.2⟩

/-- Rewrite every child of `.app op cs` by `f`, when the operator is congruent in
its children and they are all well typed. Each child is rewritten once. -/
def congr (op : Op) (cs : Array Node) (f : (c : Node) → Rw c)
    (hop : op.eoShape.isChildCongruent = true)
    (hwt : op.childrenTypedOfParent = true ∨ ∀ c ∈ cs.toList, c.WellTyped) :
    Rw (.app op cs) :=
  let rs : Array ((c : Node) × Rw c) := cs.map fun c => ⟨c, f c⟩
  let ds := rs.map (·.2.1)
  have hsize : cs.size = ds.size := by simp [ds, rs]
  ⟨.app op ds, .congr hsize hop hwt (fun i hi =>
    have hr : i < rs.size := by simpa [rs] using hi
    match h : rs[i] with
    | ⟨c, m, cert⟩ =>
      have e₁ : c = cs[i] := by
        have := congrArg Sigma.fst h
        simp [rs] at this
        exact this.symm
      have e₂ : m = ds[i]'(hsize ▸ hi) := by
        simp only [ds, Array.getElem_map]; exact (congrArg (fun x => x.2.1) h).symm
      cast (by rw [e₁, e₂]) cert) (.refl _)⟩

/-- `congr` with the rewrites of the children given in order, as a list. -/
def congrList (op : Op) (cs : Array Node) (rs : List ((c : Node) × Rw c))
    (hrs : rs.map (·.1) = cs.toList) (hop : op.eoShape.isChildCongruent = true)
    (hwt : op.childrenTypedOfParent = true ∨ ∀ c ∈ cs.toList, c.WellTyped) :
    Rw (.app op cs) :=
  let ds : Array Node := (rs.map (·.2.1)).toArray
  have hlen : rs.length = cs.size := by
    have := congrArg List.length hrs; simpa using this
  have hsize : cs.size = ds.size := by simp [ds, hlen]
  ⟨.app op ds, .congr hsize hop hwt (fun i hi =>
    have hr : i < rs.length := by omega
    have e₀ : rs[i].1 = cs[i] := by
      have := congrArg (·[i]?) hrs
      simp only [List.getElem?_map, List.getElem?_eq_getElem hr, Option.map_some,
        Array.getElem?_toList] at this
      rw [Array.getElem?_eq_getElem hi] at this
      exact Option.some.inj this
    have e₃ : rs[i].2.1 = ds[i]'(hsize ▸ hi) := by simp [ds]
    match h : rs[i] with
    | ⟨c, m, cert⟩ =>
      have e₁ : c = cs[i] := by rw [h] at e₀; exact e₀
      have e₂ : m = ds[i]'(hsize ▸ hi) := by rw [h] at e₃; exact e₃
      cast (by rw [e₁, e₂]) cert) (.refl _)⟩

end Rw

/-- The right-hand side of `(= l r)`. -/
def eqRhs? : Term → Option Term
  | .Apply (.Apply (.UOp UserOp.eq) _) r => some r
  | _ => none

/-- The name of the rule of the last step of `cs`, for profiling. -/
def lastRuleName : CCmdList → String
  | .cons (.step r _ _) .nil | .cons (.step_pop r _ _) .nil => ruleName r
  | .cons _ .nil | .nil => "?"
  | .cons _ cs => lastRuleName cs

/-- Run `cs`. If it proves `(= n r)` and `r` reads back as a node `m`, return `m`,
certified. Each phase is a profiling probe, keyed by the rule of the last step.
`r` is read back only if it is not the translation of `guess?`. -/
def applyCmds (cs : CCmdList) (n : Node) (guess? : Option Node := none) : Option (Rw n) :=
  let rule := fun (_ : Unit) => lastRuleName cs
  let rejected (_ : Unit) : Option (Rw n) := Profile.time "checker: rejected" rule fun _ => none
  if hT : Profile.time "checker: side conditions" rule
      (fun _ => decide (CmdListTranslationOk cs)) = true then
    let st := Profile.time "checker: run" rule fun _ => runFromEmpty cs
    if hC : __eo_state_is_closed st = true then
      let P := __eo_state_proven_nth st 0
      let g := guess?.getD n
      if hG : Profile.time "checker: compare" rule
          (fun _ => guess?.isSome && decide (P = eqFormula n g)) = true then
        some ⟨g, .step cs ⟨of_decide_eq_true hT, hC, of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hG).2⟩
          (.refl g)⟩
      else match Profile.time "checker: read back" rule fun _ => eqRhs? P >>= Node.ofEo n.vars with
      | some m =>
        if hE : Profile.time "checker: compare" rule (fun _ => decide (P = eqFormula n m)) = true then
          some ⟨m, .step cs ⟨of_decide_eq_true hT, hC, of_decide_eq_true hE⟩ (.refl m)⟩
        else rejected ()
      | none => rejected ()
    else rejected ()
  else rejected ()

/-- `applyCmds` for a result `m` known in advance, which is not read back. -/
def applyCmdsTo (cs : CCmdList) (n m : Node) : Option (Rw n) :=
  let rule := fun (_ : Unit) => lastRuleName cs
  let rejected (_ : Unit) : Option (Rw n) := Profile.time "checker: rejected" rule fun _ => none
  if hT : Profile.time "checker: side conditions" rule
      (fun _ => decide (CmdListTranslationOk cs)) = true then
    let st := Profile.time "checker: run" rule fun _ => runFromEmpty cs
    if hC : __eo_state_is_closed st = true then
      if hE : Profile.time "checker: compare" rule
          (fun _ => decide (__eo_state_proven_nth st 0 = eqFormula n m)) = true then
        some ⟨m, .step cs ⟨of_decide_eq_true hT, hC, of_decide_eq_true hE⟩ (.refl m)⟩
      else rejected ()
    else rejected ()
  else rejected ()

/-- A list of terms as a rule's argument list. -/
def toArgList : List Term → CArgList
  | [] => .nil
  | t :: ts => .cons t (toArgList ts)

/-- Apply one CPC rule, with the given arguments and no premises, to `n`. -/
def applyRule (r : CRule) (args : List Node) (n : Node) : Option (Rw n) :=
  applyCmds (.cons (.step r (toArgList (args.map Node.toEo)) .nil) .nil) n

end Telos
