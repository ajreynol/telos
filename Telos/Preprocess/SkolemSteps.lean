import Telos.Rewriter.Rewriter
import Telos.Rewriter.Theory.Common
import Telos.Core.Proof.Emit

/-!
# Certified steps that introduce skolems

Preprocessing replaces terms by skolems and adds lemmas about them. Both are
certified rewrites (`Rw`), so the pipeline stays a certified rewrite of the
input conjunction (`Telos/Preprocess/Pipeline.lean`) and needs no new theorem:

* replacing `t` by its purification skolem is the rewrite `t → (@purify t)`,
  by `skolem_intro` (`(= (@purify t) t)`) and `symm`;
* a lemma `L` proven by CPC steps is the rewrite `true → L`, by `true_intro`
  (`(= L true)`) and `symm`. It takes the place of a `true` conjunct of the
  pipeline (`Pipeline.pushLemmas`).
-/

namespace Telos.Preprocess

open Eo Node

/-- A list of commands as a `CCmdList`. -/
def cmdList (cs : List CCmd) : CCmdList := cs.foldr .cons .nil

/-- The premise list of the previous step only. -/
def prevPremise : CIndexList := .cons 0 .nil

/-- The CPC step `(r args)` on the terms `args`, with no premises. -/
def stepWith (r : CRule) (args : List Term) : CCmd := .step r (toArgList args) .nil

/-- `t` rewritten to its purification skolem `(@purify t)`: `skolem_intro`, then
`symm`. -/
def purifyStep (t : Node) : Option (Rw t) :=
  applyCmds (cmdList [stepWith .skolem_intro [(mkPurifySkolem t).toEo],
    .step .symm .nil prevPremise]) t

/-- The lemma proven by `cs` (its last fact), as a rewrite of `true`. -/
def lemmaBy (cs : List CCmd) : Option (Rw mkTrue) :=
  applyCmds (cmdList (cs ++ [.step .true_intro .nil prevPremise, .step .symm .nil prevPremise]))
    mkTrue

/-- The occurrences of `t` in `n` rewritten by `r`, by congruence. -/
partial def replaceRw (t : Node) (r : Rw t) (n : Node) : Rw n :=
  if h : n = t then h ▸ r
  else rewriteChildren (m := Id) (fun c => replaceRw t r c) n

/-- The CPC step `(and_elim i)` on the previous fact. -/
def andElim (i : Int) : CCmd := .step .and_elim (toArgList [.Numeral i]) prevPremise

/-- The conjuncts of the lemma `l`, flattened, each a certified rewrite of
`true`: the proof of `l` (`Proof.cmdsOf`), then `true_elim` and `and_elim`. So
`push_back`'s splitting of a lemma costs a check of small proofs, not a
reordering of the whole pipeline. A conjunction whose proof cannot be
rechecked stays whole. -/
partial def splitLemma (l : Rw mkTrue) : List (Rw mkTrue) :=
  match l.1 with
  | .app (.kind .AND) cs =>
    match Proof.cmdsOf l with
    | some cmds =>
      let base := cmds ++ [.step .symm .nil prevPremise, .step .true_elim .nil prevPremise]
      let parts := (List.range cs.size).map fun j => lemmaBy (base ++ [andElim (Int.ofNat j)])
      if parts.all Option.isSome then (parts.filterMap id).flatMap splitLemma else [l]
    | none => [l]
  | _ => [l]

end Telos.Preprocess
