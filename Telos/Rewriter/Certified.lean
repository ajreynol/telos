import Telos.Node.OfEo
import Telos.Node.DecEq
import Cpc.TranslationChecks

/-!
# Certified rewrite steps

Every rewrite telos performs is justified by CPC. A step from `n` to `m` is a
CPC command list `cs` that Logos's checker, run from the empty state, accepts,
and whose last proven fact is `(= n m)` (`ProvesEq`). `Certified n m` chains such
steps.

The certificate is checked by running Logos's own checker
(`__eo_invoke_cmd_list`), which Logos proves sound for every CPC rule. So
`Certified n m` implies that `n` and `m` are equivalent
(`Certified.equiv`, `verification/TelosProofs/Certified.lean`), with no proof per
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
operator. The proof is erased at run time; the command lists are not kept (yet). -/
inductive Certified : Node → Node → Prop
  | refl (n : Node) : Certified n n
  /-- A CPC-checked step at the top. -/
  | step {n k m : Node} (cs : CCmdList) : ProvesEq cs n k → Certified k m → Certified n m
  /-- A rewrite of the child `i` of an application whose operator is congruent
  in its children (`Node.Equiv.congr`), all of which are well typed. -/
  | congrArg {op : Op} {cs : Array Node} {m : Node} (i : Nat) (c' : Node) (hi : i < cs.size) :
      op.eoShape.isChildCongruent = true → (∀ c ∈ cs.toList, c.WellTyped) →
      Certified cs[i] c' → Certified (.app op (cs.set i c')) m → Certified (.app op cs) m

theorem Certified.trans {a b c : Node} (h₁ : Certified a b) (h₂ : Certified b c) :
    Certified a c := by
  induction h₁ with
  | refl => exact h₂
  | step cs h _ ih => exact .step cs h (ih h₂)
  | congrArg i c' hi hop hwt hc _ _ ih => exact .congrArg i c' hi hop hwt hc (ih h₂)

/-- The right-hand side of `(= l r)`. -/
def eqRhs? : Term → Option Term
  | .Apply (.Apply (.UOp UserOp.eq) _) r => some r
  | _ => none

/-- Run `cs`. If it proves `(= n r)` and `r` reads back as a node `m`, return `m`,
certified. -/
def applyCmds (cs : CCmdList) (n : Node) : Option { m // Certified n m } :=
  if hT : CmdListTranslationOk cs then
    if hC : __eo_state_is_closed (runFromEmpty cs) = true then
      let P := __eo_state_proven_nth (runFromEmpty cs) 0
      match eqRhs? P >>= Node.ofEo n.vars with
      | some m =>
        if hE : P = eqFormula n m then some ⟨m, .step cs ⟨hT, hC, hE⟩ (.refl m)⟩
        else none
      | none => none
    else none
  else none

/-- A list of terms as a rule's argument list. -/
def toArgList : List Term → CArgList
  | [] => .nil
  | t :: ts => .cons t (toArgList ts)

/-- Apply one CPC rule, with the given arguments and no premises, to `n`. -/
def applyRule (r : CRule) (args : List Node) (n : Node) : Option { m // Certified n m } :=
  applyCmds (.cons (.step r (toArgList (args.map Node.toEo)) .nil) .nil) n

end Telos
