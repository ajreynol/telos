import Cpc.Spec
import Cpc.Logos
import Cpc.TranslationChecks
import Telos.Node.ToEo

/-!
# The Logos theorems telos builds on

telos's proofs use a few theorems of Logos's proofs (`Cpc/Proofs/`): its
checker's soundness, which covers every CPC rule, its congruence over
application spines, and some facts about SMT typing and values. Those proofs are
most of Logos and expensive to build, and the theorems rest on Logos's type
preservation development.

So that telos's proofs build without them, the theorems are restated here, over
Logos's *definitions* only, as the fields of the class `LogosFacts`. Theorems
that need them take `[LogosFacts]`, and the main theorem is
`Telos.rewrite_correct_of_logos`. `TelosFull/Main.lean` (`lake build TelosFull`)
imports Logos's proofs and proves the instance, field by field from the Logos
theorem it restates. This keeps the statements in sync with the pinned Logos, and
gives the unconditional `Telos.rewrite_correct`.

The definitions below are Logos's (`RuleProofs.smt_value_rel`,
`RuleProofs.eo_has_smt_translation`, `RuleProofs.eo_has_bool_type`), copied.
Logos's `eo_interprets M t true` is an inductive of its proofs, so it is written
here unfolded (`TrueIn`: `t` has type `Bool` and evaluates to `true`).
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- Logos's `smt_value_rel`: the values are equal (extensionally, for regular
languages). -/
def SmtValueRel (v w : SmtValue) : Prop :=
  __smtx_model_eval_eq v w = SmtValue.Boolean true

/-- Logos's `eo_has_smt_translation`: `t` has an SMT type. -/
def HasSmtType (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Logos's `eo_has_bool_type`. -/
def HasBoolType (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-- `t` is true in `M` (Logos's `eo_interprets M t true`, for a Boolean `t`). -/
def TrueIn (M : SmtModel) (t : Term) : Prop :=
  __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true

/-- `t` is a valid formula: Boolean, and true in every well-formed model. -/
def Valid (t : Term) : Prop :=
  HasBoolType t ∧ ∀ M, model_wf M → TrueIn M t

/-- The CPC formula `(= a b)` (Logos's `mkEq`). -/
def mkEq (a b : Term) : Term := eoApp2 UserOp.eq a b

/-- The Logos theorems telos uses, restated. `TelosFull/Main.lean` proves the
instance from Logos's proofs; the name of each Logos theorem is in its field's
documentation. -/
class LogosFacts : Prop where
  /-- `proven_from_empty_valid`: a fact proven by a command list run from the
  empty checker state is valid. -/
  checker_sound : ∀ (cs : CCmdList) (P : Term),
    CmdListTranslationOk cs →
    __eo_state_is_closed (__eo_invoke_cmd_list CState.nil cs) = true →
    __eo_state_proven_nth (__eo_invoke_cmd_list CState.nil cs) 0 = P →
    Valid P
  /-- `CongSupport.cong_spine_valid`: spines with valid pairwise equal arguments
  are validly equal. -/
  cong_spine : ∀ (head : Term) (xs ys : List Term),
    HasSmtType (xs.foldl Term.Apply head) →
    List.Forall₂ (fun x y => Valid (mkEq x y)) xs ys →
    Valid (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head))
  /-- `RuleProofs.eq_valid_iff`: an equation is valid iff its sides have the
  same SMT type and related values in every well-formed model. -/
  eq_valid_iff : ∀ (a b : Term),
    Valid (mkEq a b) ↔
      (__smtx_typeof (__eo_to_smt a) ≠ SmtType.None ∧
        __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b)) ∧
      ∀ M, model_wf M →
        SmtValueRel (__smtx_model_eval M (__eo_to_smt a)) (__smtx_model_eval M (__eo_to_smt b))
  /-- `RuleProofs.smt_value_rel_refl`. -/
  value_rel_refl : ∀ v, SmtValueRel v v
  /-- `RuleProofs.smt_value_rel_symm`. -/
  value_rel_symm : ∀ v w, SmtValueRel v w → SmtValueRel w v
  /-- `RuleProofs.smt_value_rel_trans`. -/
  value_rel_trans : ∀ u v w, SmtValueRel u v → SmtValueRel v w → SmtValueRel u w
  /-- `SpineArgsSupport.spine_args_have_smt_translation`, for `and` and `or`:
  the tail of a well-typed `(and x r)` or `(or x r)` is well typed. -/
  and_or_rest : ∀ (op : UserOp) (x r : Term), (op = UserOp.and ∨ op = UserOp.or) →
    HasSmtType (eoApp2 op x r) → HasSmtType r
  /-- `Smtm.smt_term_seq_type_wf_of_non_none`: the sequence type of a term is
  well formed. -/
  seq_type_wf : ∀ (x : SmtTerm) (A : SmtType),
    __smtx_typeof x ≠ SmtType.None → __smtx_typeof x = SmtType.Seq A →
    __smtx_type_wf (SmtType.Seq A) = true
  /-- `SubstituteSupport.eo_typeof_eq_of_smt_type_eq`, for `Bool`: a term of SMT
  type `Bool` has Eunoia type `Bool`. -/
  eo_typeof_bool : ∀ (t : Term),
    __smtx_typeof (__eo_to_smt t) = SmtType.Bool → __eo_typeof t = Term.Bool

/-! ## Facts that need no Logos proof -/

@[simp] theorem inhabited_type_bool : __smtx_inhabited_type SmtType.Bool = true := by
  simp [__smtx_inhabited_type]

@[simp] theorem inhabited_type_bitvec (w : native_Nat) :
    __smtx_inhabited_type (SmtType.BitVec w) = true := by
  simp [__smtx_inhabited_type]

theorem typeof_eq_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.eq t1 t2) =
      __smtx_typeof_eq (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_plus_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.plus t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_mult_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.mult t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_concat_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.concat t1 t2) =
      __smtx_typeof_concat (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def]

theorem model_eval_eq_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

theorem model_eval_not_eq (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not a) =
      __smtx_model_eval_not (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def]

theorem typeof_eq_eq_bool_iff (T U : SmtType) :
    __smtx_typeof_eq T U = SmtType.Bool ↔ T ≠ SmtType.None ∧ T = U := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None <;> by_cases hTU : T = U <;>
    simp [native_ite, native_Teq, hT, hTU]

end Telos
