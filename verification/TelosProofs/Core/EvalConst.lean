import TelosProofs.Core.Template
import TelosProofs.Core.AciConcat
import Telos.Core.EvalConst

/-!
# Evaluation of an operator over constants is a CPC step

`evalConst_provesEq`: under `EvalConst.Ok n m` (`Telos/Core/EvalConst.lean`),
the step `(evaluate n)` is accepted by Logos's checker and proves `(= n m)`.
The core is `value_eval`: Logos's evaluator `__run_evaluate` takes the
translation of `n` to that of its value `m`, one case per operator.
-/

open Eo Smtm SmtEval

namespace Telos

namespace EvalConstProof

open Template
open EvalConst

/-! ## Logos's evaluator on constants and sums -/

theorem run_numeral (i : Int) : __run_evaluate (Term.Numeral i) = Term.Numeral i := by
  simp [__run_evaluate]
theorem run_rational (q : Rat) : __run_evaluate (Term.Rational q) = Term.Rational q := by
  simp [__run_evaluate]
theorem run_string (s : List Nat) : __run_evaluate (Term.String s) = Term.String s := by
  simp [__run_evaluate]
theorem run_boolean (b : Bool) : __run_evaluate (Term.Boolean b) = Term.Boolean b := by
  simp [__run_evaluate]

theorem run_sum : ∀ is : List Int,
    __run_evaluate (eoRightAssocNil .plus (Term.Numeral 0) (is.map Term.Numeral)) = Term.Numeral is.sum
  | [] => by simp [eoRightAssocNil, run_numeral]
  | i :: is => by
    simp only [List.map_cons, eoRightAssocNil, eoApp2]
    rw [__run_evaluate, run_numeral, run_sum is]
    simp [__eo_add, native_zplus]

theorem run_qsum : ∀ qs : List Rat,
    __run_evaluate (eoRightAssocNil .plus (Term.Rational (native_mk_rational 0 1)) (qs.map Term.Rational)) =
      Term.Rational qs.sum
  | [] => by simp [eoRightAssocNil, run_rational, native_mk_rational]
  | q :: qs => by
    simp only [List.map_cons, eoRightAssocNil, eoApp2]
    rw [__run_evaluate, run_rational, run_qsum qs]
    simp [__eo_add, native_qplus]

theorem run_cat : ∀ ss : List (List Nat),
    __run_evaluate (eoRightAssocNil .str_concat (Term.String []) (ss.map Term.String)) = Term.String ss.flatten
  | [] => by simp [eoRightAssocNil, run_string]
  | s :: ss => by
    simp only [List.map_cons, eoRightAssocNil, eoApp2]
    rw [__run_evaluate, run_string, run_cat ss]
    simp [__eo_concat, native_str_concat]

/-! ## The constants of a list -/

theorem ints_eq : ∀ {cs : List Node} {is : List Int}, ints cs = some is →
    cs = is.map fun i => Node.const (.integer i)
  | [], is, h => by simp [ints] at h; subst h; rfl
  | c :: cs, is, h => by
    unfold ints at h
    split at h
    next heq => simp at heq
    next heq =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨is', h', rfl⟩ := h
      rw [ints_eq h']; rfl
    next => simp at h

theorem rats_eq : ∀ {cs : List Node} {qs : List Rat}, rats cs = some qs →
    cs = qs.map fun q => Node.const (.rational q)
  | [], qs, h => by simp [rats] at h; subst h; rfl
  | c :: cs, qs, h => by
    unfold rats at h
    split at h
    next heq => simp at heq
    next heq =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨qs', h', rfl⟩ := h
      rw [rats_eq h']; rfl
    next => simp at h

theorem strs_eq : ∀ {cs : List Node} {ss : List (List Nat)}, strs cs = some ss →
    cs = ss.map fun s => Node.const (.string s)
  | [], ss, h => by simp [strs] at h; subst h; rfl
  | c :: cs, ss, h => by
    unfold strs at h
    split at h
    next heq => simp at heq
    next heq =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ss', h', rfl⟩ := h
      rw [strs_eq h']; rfl
    next => simp at h

/-! ## Translations -/

theorem typeof_numeral (i : Int) : __smtx_typeof (__eo_to_smt (Term.Numeral i)) = SmtType.Int := by
  show __smtx_typeof (SmtTerm.Numeral i) = _
  rw [__smtx_typeof.eq_def]
theorem typeof_rational (q : Rat) : __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Real := by
  show __smtx_typeof (SmtTerm.Rational q) = _
  rw [__smtx_typeof.eq_def]

theorem toEo_add_ints {is : List Int} (h : 2 ≤ is.length) :
    (Node.app (.kind .ADD) ⟨is.map fun i => Node.const (.integer i)⟩).toEo =
      eoRightAssocNil .plus (Term.Numeral 0) (is.map Term.Numeral) := by
  match is, h with
  | i :: j :: is, _ =>
    rw [Node.toEo_app]
    simp only [Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval, typedNil, List.map_map]
    simp [Function.comp_def, Node.toEo, Const.toEo, typeof_numeral, typedNilOfType]

theorem toEo_add_rats {qs : List Rat} (h : 2 ≤ qs.length) :
    (Node.app (.kind .ADD) ⟨qs.map fun q => Node.const (.rational q)⟩).toEo =
      eoRightAssocNil .plus (Term.Rational (native_mk_rational 0 1)) (qs.map Term.Rational) := by
  match qs, h with
  | p :: q :: qs, _ =>
    rw [Node.toEo_app]
    simp only [Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval, typedNil, List.map_map]
    simp [Function.comp_def, Node.toEo, Const.toEo, typeof_rational, typedNilOfType]

/-- A well-typed concatenation's first component is well typed. -/
theorem concat_head_typed {c : Node} {cs : List Node}
    (h : (Node.app (.kind .STRING_CONCAT) ⟨c :: cs⟩).smtTypeF ≠ SmtType.None) (h2 : cs ≠ []) :
    c.smtTypeF ≠ SmtType.None := by
  rw [Node.smtTypeF_eq] at h ⊢
  intro hc
  apply h
  match cs, h2 with
  | d :: ds, _ =>
    show __smtx_typeof (__eo_to_smt (Node.app (.kind .STRING_CONCAT) ⟨c :: d :: ds⟩).toEo) = _
    rw [Node.toEo_app]
    show __smtx_typeof (SmtTerm.str_concat (__eo_to_smt c.toEo) _) = _
    rw [__smtx_typeof.eq_def]
    show __smtx_typeof_seq_op_2 (__smtx_typeof (__eo_to_smt c.toEo)) _ = _
    rw [show __smtx_typeof (__eo_to_smt c.toEo) = SmtType.None from hc]
    rfl

theorem string_type {s : List Nat} (h : (Node.const (.string s)).smtTypeF ≠ SmtType.None) :
    (Node.const (.string s)).smtTypeF = SmtType.Seq SmtType.Char := by
  rw [Node.smtTypeF_eq] at h ⊢
  revert h
  unfold Node.smtType Node.toSmt
  rw [show __eo_to_smt (Node.const (.string s)).toEo = SmtTerm.String s by simp [Node.toEo, Const.toEo]; rfl]
  rw [__smtx_typeof.eq_def]
  simp only [native_ite]
  split <;> simp

/-! ## The value -/

theorem neg_iff_not (x : Int) : decide (x < 0) = !decide (0 ≤ x) := by
  by_cases h : 0 ≤ x
  · simp [h]
  · simp [h]; omega

theorem geq_int (a b : Int) : (decide (b < a) || decide ((0 : Rat) = ↑b + -↑a)) = decide (b ≤ a) := by
  have h : ((0 : Rat) = ↑b + -↑a) ↔ a = b := by
    constructor
    · intro h
      have : (a : Rat) = b := by linarith
      exact_mod_cast this
    · rintro rfl; simp
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, h]
  exact ⟨fun h => h.elim le_of_lt (fun e => e ▸ le_refl _), fun h => (lt_or_eq_of_le h).imp id Eq.symm⟩

theorem geq_rat (a b : Rat) : (decide (b < a) || decide ((0 : Rat) = b + -a)) = decide (b ≤ a) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · left; linarith
    · right; rw [h]; ring

/-- **Logos's evaluator computes the value.** -/
theorem value_eval {n m : Node} (hv : value n = some m) (hn : n.smtTypeF ≠ SmtType.None) :
    __run_evaluate n.toEo = m.toEo := by
  match n, hv with
  | .app (.kind k) ⟨cs⟩, hv =>
    simp only [value] at hv
    unfold valueOf at hv
    split at hv <;> try simp only [Option.some.injEq, reduceCtorEq] at hv
    · -- not
      subst hv
      rw [toEo_spine1 rfl]
      simp [__run_evaluate, run_boolean, __eo_not, native_not, EvalConst.bool, Node.toEo, Const.toEo]
    · -- =
      rename_i a b
      split at hv
      · rename_i hk
        simp only [Option.some.injEq] at hv
        subst hv
        rw [toEo_spine2 rfl]
        cases a <;> cases b <;> simp_all [sameKind, __run_evaluate, __eo_eq, native_teq, __eo_ite, __eo_and,
          __eo_is_q, __eo_is_z, __eo_is_bin, __eo_is_str, __eo_is_bool, __eo_is_q_internal,
          __eo_is_z_internal, __eo_is_bin_internal, __eo_is_str_internal, __eo_is_bool_internal,
          native_and, native_not, native_ite, EvalConst.bool, Node.toEo, Const.toEo, eq_comm]
      · simp at hv
    · -- >= of integers
      subst hv
      rw [toEo_spine2 rfl]
      simp [__run_evaluate, __eo_add, __eo_neg, __eo_is_neg, __eo_or, __eo_eq, __eo_to_q, native_teq,
        native_zlt, native_zplus, native_zneg, native_or, native_to_real, native_mk_rational, EvalConst.bool,
        Node.toEo, Const.toEo, geq_int]
    · -- >= of rationals
      subst hv
      rw [toEo_spine2 rfl]
      simp [__run_evaluate, __eo_add, __eo_neg, __eo_is_neg, __eo_or, __eo_eq, __eo_to_q, native_teq,
        native_qlt, native_qplus, native_qneg, native_or, native_mk_rational, EvalConst.bool, Node.toEo, Const.toEo,
        geq_rat]
    · -- str.len
      subst hv
      rw [toEo_spine1 rfl]
      simp [__run_evaluate, __eo_len, native_str_len, Node.toEo, Const.toEo]
    · -- str.contains
      subst hv
      rw [toEo_spine2 rfl]
      simp [__run_evaluate, __eo_find, __eo_is_neg, __eo_not, native_zlt, native_not, EvalConst.bool,
        Node.toEo, Const.toEo, neg_iff_not]
    · -- +
      rename_i x y rest
      split at hv
      · rename_i is his
        simp only [Option.some.injEq] at hv
        subst hv
        have e := ints_eq his
        have hl : 2 ≤ is.length := by
          have := congrArg List.length e; simp at this; omega
        simp only [e]
        rw [toEo_add_ints hl, run_sum]; simp [Node.toEo, Const.toEo]
      · rename_i hnone
        simp only [Option.map_eq_some_iff] at hv
        obtain ⟨qs, hqs, rfl⟩ := hv
        have e := rats_eq hqs
        have hl : 2 ≤ qs.length := by
          have := congrArg List.length e; simp at this; omega
        simp only [e]
        rw [toEo_add_rats hl, run_qsum]; simp [Node.toEo, Const.toEo]
    · -- str.++
      rename_i x y rest
      simp only [Option.map_eq_some_iff] at hv
      obtain ⟨ss, hss, rfl⟩ := hv
      have e := strs_eq hss
      match ss, e with
      | s :: t :: ss, e =>
        have hs : (Node.const (.string s)).smtTypeF = SmtType.Seq SmtType.Char := by
          apply string_type
          simp only [List.map_cons] at e
          rw [e] at hn
          exact concat_head_typed hn (by simp)
        have hc : AciConcat.isConcat ⟨x :: y :: rest⟩ = true := by
          simp only [List.map_cons] at e
          rw [e]
          simp only [AciConcat.isConcat, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨by simp, ?_⟩
          simpa using hs
        rw [AciConcatProof.toEo_concat hc, e]
        simp only [List.map_map]
        have : ((fun c : Node => c.toEo) ∘ fun s : List Nat => Node.const (.string s)) = Term.String := by
          funext s; simp [Node.toEo, Const.toEo]
        rw [this]
        exact (run_cat _).trans (by simp [Node.toEo, Const.toEo])

/-! ## The step -/

theorem typeof_eq_sides {T U : SmtType} (h : __smtx_typeof_eq T U = SmtType.Bool) :
    T ≠ SmtType.None ∧ U ≠ SmtType.None := by
  unfold __smtx_typeof_eq __smtx_typeof_guard at h
  cases T <;> cases U <;> simp_all [native_ite, native_Teq]

/-- **An evaluation step over constants is a CPC step.** -/
theorem evalConst_provesEq [LogosFacts] {n m : Node} (h : EvalConst.Ok n m) :
    ProvesEq (.cons (.step .evaluate (.cons n.toEo .nil) .nil) .nil) n m := by
  obtain ⟨hv, hty⟩ := h
  have hty' : __smtx_typeof (__eo_to_smt (eqFormula n m)) = SmtType.Bool := by
    rw [Node.smtTypeF_eq] at hty; rw [← toEo_eq]; exact hty
  have hsides := typeof_eq_sides (by rw [← Node.typeof_eqFormula]; exact hty')
  have hn : n.smtTypeF ≠ SmtType.None := by rw [Node.smtTypeF_eq]; exact hsides.1
  have hm : m.smtTypeF ≠ SmtType.None := by rw [Node.smtTypeF_eq]; exact hsides.2
  have hT : cmdTranslationOk (.step .evaluate (.cons n.toEo .nil) .nil) := by
    refine ⟨?_, trivial⟩
    have := hn; rw [Node.smtTypeF_eq] at this; exact this
  refine provesEq_one hT ?_ hty'
  show __eo_prog_evaluate n.toEo = _
  have hn' := toEo_ne_stuck hn
  have hm' := toEo_ne_stuck hm
  unfold __eo_prog_evaluate
  split
  next h => exact absurd h hn'
  next =>
    rw [value_eval hv hn]
    simp [__eo_mk_apply, eqFormula, eoApp2]

end EvalConstProof

end Telos
