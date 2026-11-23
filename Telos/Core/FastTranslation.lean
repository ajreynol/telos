import Telos.Core.Node.SmtTypeFast
import Cpc.TranslationChecks

/-!
# Deciding the translation side conditions fast

Logos's checker requires of each argument of a rule that its translation to an
SMT term is well typed (`CmdListTranslationOk`, `eoHasSmtTranslation t`:
`__smtx_typeof (__eo_to_smt t) ≠ None`). Cpc decides it by translating and
typing. The translation of a component skolem of a membership's unfolding,
`(@re_unfold_pos_component s r i)`, is the `i`-th component of `s` written with
`str.substr` and `str.indexof_re_split`: `s` occurs three times at each of the
`i` levels, so the term, shared in memory, is exponential as a tree, and so is
its typing, which does not share. Unfoldings nest these skolems in one another.

`termTyF t` is the type of `t`'s translation (`termTyF_eq`), computed without
translating the skolems: the type of a component is that of the string and the
regular expression's components (`compTy_eq`); a term with such a skolem is
typed from its children's types by the typing rules of the operators above
the skolems (`termTy_*`), and a term without one by Logos, as before.

The instances below decide the side conditions as Cpc's do, derived from their
definitions the same way, with `termTyF` for the typing of a term; their
priority makes the checks of the rewriter and of the proofs use them.
-/

open Eo Smtm SmtEval

namespace Telos.FastTr

open Telos.Node (termTy termTyF termTyF_eq)

/-! ## The side conditions, decided with `termTyF` -/

instance (priority := high) decEoHasSmtTranslationF (t : Term) : Decidable (eoHasSmtTranslation t) :=
  decidable_of_iff (termTyF t ≠ SmtType.None) (by rw [termTyF_eq]; rfl)

/-- `eoListAllHaveSmtTranslationB`, with `termTyF`. -/
def listOkF : Term → Bool
  | Term.__eo_List_nil => true
  | Term.Apply (Term.Apply Term.__eo_List_cons t) ts => decide (termTyF t ≠ .None) && listOkF ts
  | _ => false

theorem listOkF_iff : ∀ t : Term, listOkF t = true ↔ EoListAllHaveSmtTranslation t := by
  intro t
  fun_induction listOkF t <;>
    simp_all [EoListAllHaveSmtTranslation, eoHasSmtTranslation, termTyF_eq, Node.termTy]

instance (priority := high) decEoListAllF (t : Term) : Decidable (EoListAllHaveSmtTranslation t) :=
  decidable_of_iff _ (listOkF_iff t)

instance (priority := high) decArgMaskedF (k : ArgTranslationKind) (t : Term) :
    Decidable (argTranslationOkMasked k t) :=
  match k with
  | .term => inferInstanceAs (Decidable (eoHasSmtTranslation t))
  | .list => inferInstanceAs (Decidable (EoListAllHaveSmtTranslation t))
  | .type => inferInstanceAs (Decidable (__smtx_type_wf (__eo_to_smt_type t) = true))
  | .wfTerm => decidable_of_iff (termTyF t ≠ .None ∧ __smtx_type_wf (termTyF t) = true)
      (by simp only [argTranslationOkMasked, eoHasSmtTranslation, termTyF_eq, Node.termTy])
  | .wfElem => decidable_of_iff (__smtx_type_wf_component (termTyF t) = true)
      (by simp only [argTranslationOkMasked, termTyF_eq, Node.termTy])

instance (priority := high) decCArgListF : (args : CArgList) → Decidable (cArgListTranslationOk args)
  | CArgList.nil => isTrue trivial
  | CArgList.cons a args =>
    have := decCArgListF args
    inferInstanceAs (Decidable (eoHasSmtTranslation a ∧ cArgListTranslationOk args))

instance (priority := high) decCArgListMaskF :
    (mask : List ArgTranslationKind) → (args : CArgList) → Decidable (cArgListTranslationOkMask mask args)
  | [], CArgList.nil => isTrue trivial
  | k :: mask, CArgList.cons a args =>
    have := decCArgListMaskF mask args
    inferInstanceAs (Decidable (argTranslationOkMasked k a ∧ cArgListTranslationOkMask mask args))
  | [], CArgList.cons _ _ => isFalse not_false
  | _ :: _, CArgList.nil => isFalse not_false

instance (priority := high) decCmdF (c : CCmd) : Decidable (cmdTranslationOk c) := by
  unfold cmdTranslationOk; split <;> infer_instance

instance (priority := high) decCmdListF : (cmds : CCmdList) → Decidable (CmdListTranslationOk cmds)
  | CCmdList.nil => isTrue CmdListTranslationOk.nil
  | CCmdList.cons c cmds =>
    if hc : cmdTranslationOk c then
      match decCmdListF cmds with
      | isTrue hcs => isTrue (CmdListTranslationOk.cons c cmds hc hcs)
      | isFalse hcs => isFalse fun h => hcs (by cases h; assumption)
    else isFalse fun h => hc (by cases h; assumption)

end Telos.FastTr
