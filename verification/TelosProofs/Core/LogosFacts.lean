import Cpc.Spec
import Cpc.Logos
import Cpc.TranslationChecks
import Telos.Core.Node.ToEo

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

/-- Logos's `Smtm.type_has_no_none_components`: no component of the type is
`None` (or an unresolved reference). -/
def NoNoneParts : SmtType → Prop
  | SmtType.None => False
  | SmtType.TypeRef _ => False
  | SmtType.Seq A => NoNoneParts A
  | SmtType.Set A => NoNoneParts A
  | SmtType.Map A B => NoNoneParts A ∧ NoNoneParts B
  | SmtType.FunType A B => NoNoneParts A ∧ NoNoneParts B
  | SmtType.DtcAppType A B => NoNoneParts A ∧ NoNoneParts B
  | _ => True

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

/-- Logos's `model_agrees_on_globals`: the models differ only in the values of
variables (`Term.Var`, bound variables). -/
structure AgreesOnGlobals (M N : SmtModel) : Prop where
  consts : ∀ s T, native_model_lookup M s T = native_model_lookup N s T
  funs : ∀ fid T U, model_fun_lookup M fid T U = model_fun_lookup N fid T U
  usortDom : M.usortDom = N.usortDom

/-- Logos's `NotTopLevelQuantifier`: `t` is not a quantifier. -/
def NotTopLevelQuantifier (t : Term) : Prop :=
  (∀ xs body, t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ∧
  (∀ xs body, t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)

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
  /-- `type_preservation` and `bool_value_canonical`: in a well-formed model, a
  term of SMT type `Bool` evaluates to a Boolean. -/
  eval_bool : ∀ (M : SmtModel) (t : SmtTerm), model_wf M →
    __smtx_typeof t = SmtType.Bool → ∃ b, __smtx_model_eval M t = SmtValue.Boolean b
  /-- `type_preservation` and `real_value_canonical`: in a well-formed model, a
  term of SMT type `Real` evaluates to a real. -/
  eval_real : ∀ (M : SmtModel) (t : SmtTerm), model_wf M →
    __smtx_typeof t = SmtType.Real → ∃ r, __smtx_model_eval M t = SmtValue.Real r
  /-- `type_preservation` and `int_value_canonical`: in a well-formed model, a
  term of SMT type `Int` evaluates to an integer. -/
  eval_int : ∀ (M : SmtModel) (t : SmtTerm), model_wf M →
    __smtx_typeof t = SmtType.Int → ∃ i, __smtx_model_eval M t = SmtValue.Numeral i
  /-- `CongSupport.congTrueSpine_eq_true`: congruence of an application spine in
  one model, for a spine that is not a quantifier, from argument equalities that
  are true in every model agreeing with it on the globals. -/
  cong_spine_model : ∀ (M : SmtModel), model_wf M → ∀ (head : Term) (xs ys : List Term),
    NotTopLevelQuantifier (xs.foldl Term.Apply head) →
    HasBoolType (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head)) →
    List.Forall₂ (fun x y => HasBoolType (mkEq x y) ∧
      ∀ N, model_wf N → AgreesOnGlobals M N → TrueIn N (mkEq x y)) xs ys →
    TrueIn M (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head))
  /-- `CongSupport.congTypeSpine_eq_has_bool_type`: a well-typed spine and well-typed
  argument equalities give a well-typed equality of the spines. -/
  cong_type_spine : ∀ (head : Term) (xs ys : List Term),
    HasSmtType (xs.foldl Term.Apply head) →
    List.Forall₂ (fun x y => HasBoolType (mkEq x y)) xs ys →
    HasBoolType (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head))
  /-- `smt_model_eval_eq_of_eo_closed`: a closed term has the same value in models
  that agree on the globals. -/
  closed_eval : ∀ (P : Term), __eo_is_closed P = Term.Boolean true → ∀ (M N : SmtModel),
    AgreesOnGlobals M N → __smtx_model_eval M (__eo_to_smt P) = __smtx_model_eval N (__eo_to_smt P)
  /-- `SpineArgsSupport.spine_args_have_smt_translation`, for a declared function:
  the arguments of a well-typed application are well typed. -/
  uf_args : ∀ (i : native_Nat) (T : Term) (xs : List Term),
    HasSmtType (xs.foldl Term.Apply (Term.UConst i T)) → ∀ x ∈ xs, HasSmtType x
  /-- `Smtm.term_type_has_no_none_components_of_non_none`: the type of a
  well-typed term has no `None` component. -/
  type_no_none : ∀ (t : SmtTerm), __smtx_typeof t ≠ SmtType.None → NoNoneParts (__smtx_typeof t)
  /-- `Smtm.tuple_args_have_smt_translation_of_has_smt_translation`. -/
  tuple_args : ∀ (x y : Term), HasSmtType (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) →
    HasSmtType x ∧ HasSmtType y
  /-- `Smtm.apply_uop1_arg_has_smt_translation_of_has_smt_translation`: the
  argument of a well-typed application of an indexed operator. -/
  uop1_arg : ∀ (op : UserOp1) (idx x : Term), HasSmtType (Term.Apply (Term.UOp1 op idx) x) →
    HasSmtType x
  /-- `Smtm.tuple_update_index_nat_valid_and_args_have_smt_translation` and
  `Smtm.update_index_sel_and_args_have_smt_translation`. -/
  update_args : ∀ (op : UserOp1) (idx x y : Term), (op = UserOp1.tuple_update ∨ op = UserOp1.update) →
    HasSmtType (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) → HasSmtType x ∧ HasSmtType y
  /-- `Smtm.apply_dt_sel_arg_has_smt_translation_of_has_smt_translation`. -/
  dt_sel_arg : ∀ (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (x : Term),
    HasSmtType (Term.Apply (Term.DtSel s d i j) x) → HasSmtType x
  /-- The arguments of a well-typed application of a datatype constructor are
  well typed: from `CongSupport.eo_to_smt_appSpineRev_dtcons` and
  `Smtm.generic_apply_type_of_non_special_head_closed`. -/
  dt_cons_args : ∀ (s : native_String) (d : DatatypeDecl) (i : native_Nat) (xs : List Term),
    HasSmtType (xs.foldl Term.Apply (Term.DtCons s d i)) → ∀ x ∈ xs, HasSmtType x
  /-- `Smtm.type_default_typed_canonical_of_type_wf`: the default value of a
  well-formed type has that type, and is canonical. -/
  type_default_ok : ∀ (uc : SmtUSortDom), usort_dom_wf uc → ∀ (T : SmtType),
    __smtx_type_wf T = true →
    __smtx_typeof_value (__smtx_type_default T) = T ∧ __smtx_value_canonical uc (__smtx_type_default T) = true

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
