import TelosProofs.Core.CondEquiv

/-!
# Congruence under a quantifier, under a condition

A triangular substitution step (`Certified.tri`) substitutes in the body of a
quantifier (`JustKind.body`). The substituted terms are equal in the models where
the entries hold, not in every model, so the congruence of
`Node.Equiv.congr_binder` does not apply. It holds still: the condition is
stable (`StableCond`), and a model that gives a bound variable a value agrees
with the model on the globals, so the condition holds there too, and the bodies
have the same value there (`condEquiv_quant`).

Logos evaluates `(exists ((x T)) b)` to whether some value of type `T` (and
canonical) makes `b` true in the model extended with `x` (`native_eval_exists`),
and translates `(forall xs b)` as `(not (exists xs (not b)))`. Everything here is
proved from those definitions.
-/

open Eo Smtm SmtEval

namespace Telos

set_option linter.unusedSectionVars false
set_option linter.internalConstructors false

/-! ## Extending a model with a bound variable -/

/-- Giving a bound variable a value keeps the globals. -/
theorem push_agrees (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    AgreesOnGlobals M (native_model_push M s T v) :=
  ⟨fun _ _ => by simp [native_model_lookup, native_model_push, model_key], fun _ _ _ => rfl, rfl⟩

/-- Giving a bound variable a canonical value of its type keeps the model well
formed. -/
theorem push_wf {M : SmtModel} (hM : model_wf M) {s : native_String} {T : SmtType} {v : SmtValue}
    (hv : __smtx_typeof_value v = T) (hc : __smtx_value_canonical M.usortDom v = true) :
    model_wf (native_model_push M s T v) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  refine ⟨fun isVar s' T' hT => ?_, fun isVar s' T' hT => ?_, h3, h4⟩
  · simp only [native_model_push]
    split
    · rename_i e
      simp only [SmtModelKey.mk.injEq] at e
      obtain ⟨-, -, rfl⟩ := e
      exact hv
    · exact h1 isVar s' T' hT
  · simp only [native_model_push]
    split
    · exact hc
    · exact h2 isVar s' T' hT

/-! ## Existential chains -/

theorem eval_exists_congr {M : SmtModel} {s : native_String} {T : SmtType} {b b' : SmtTerm}
    (h : ∀ v, __smtx_typeof_value v = T → __smtx_value_canonical M.usortDom v = true →
      __smtx_model_eval (native_model_push M s T v) b =
        __smtx_model_eval (native_model_push M s T v) b') :
    __smtx_model_eval M (SmtTerm.exists s T b) = __smtx_model_eval M (SmtTerm.exists s T b') := by
  classical
  have hiff : (∃ v : SmtValue, __smtx_typeof_value v = T ∧
        __smtx_value_canonical M.usortDom v = true ∧
        __smtx_model_eval (native_model_push M s T v) b = SmtValue.Boolean true) ↔
      (∃ v : SmtValue, __smtx_typeof_value v = T ∧
        __smtx_value_canonical M.usortDom v = true ∧
        __smtx_model_eval (native_model_push M s T v) b' = SmtValue.Boolean true) :=
    ⟨fun ⟨v, h1, h2, h3⟩ => ⟨v, h1, h2, (h v h1 h2) ▸ h3⟩,
     fun ⟨v, h1, h2, h3⟩ => ⟨v, h1, h2, (h v h1 h2).symm ▸ h3⟩⟩
  simp only [__smtx_model_eval]
  split <;> split <;> rename_i h1 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

/-- **Congruence of an existential chain** under a stable condition: bodies with
the same value in every model where the condition holds give chains with the same
value there. -/
theorem exists_chain_congr {Φ : SmtModel → Prop} (hΦ : StableCond Φ) :
    ∀ (vs : Term) (b b' : SmtTerm),
      (∀ N, model_wf N → Φ N → __smtx_model_eval N b = __smtx_model_eval N b') →
      ∀ M, model_wf M → Φ M →
        __smtx_model_eval M (__eo_to_smt_exists vs b) =
          __smtx_model_eval M (__eo_to_smt_exists vs b') := by
  intro vs b
  induction vs, b using __eo_to_smt_exists.induct with
  | case1 F =>
    intro b' h M hM hΦM
    simp only [__eo_to_smt_exists]
    exact h M hM hΦM
  | case2 s T vs F ih =>
    intro b' h M hM hΦM
    simp only [__eo_to_smt_exists]
    apply eval_exists_congr
    intro v hv hc
    exact ih b' h _ (push_wf hM hv hc) (hΦ M _ hM (push_wf hM hv hc) (push_agrees M _ _ v) hΦM)
  | case3 vs F h1 h2 =>
    intro b' _ M _ _
    rw [__eo_to_smt_exists.eq_3 _ _ h1 h2, __eo_to_smt_exists.eq_3 _ _ h1 h2]

/-- Bodies of the same type give existential chains of the same type. -/
theorem typeof_exists_chain :
    ∀ (vs : Term) (b b' : SmtTerm), __smtx_typeof b = __smtx_typeof b' →
      __smtx_typeof (__eo_to_smt_exists vs b) = __smtx_typeof (__eo_to_smt_exists vs b') := by
  intro vs b
  induction vs, b using __eo_to_smt_exists.induct with
  | case1 F => intro b' h; simpa only [__eo_to_smt_exists] using h
  | case2 s T vs F ih =>
    intro b' h
    simp only [__eo_to_smt_exists, __smtx_typeof]
    rw [ih b' h]
  | case3 vs F h1 h2 =>
    intro b' _
    rw [__eo_to_smt_exists.eq_3 _ _ h1 h2, __eo_to_smt_exists.eq_3 _ _ h1 h2]

/-- The body of a well-typed existential chain with variables is Boolean. -/
theorem exists_chain_body_bool :
    ∀ (vs : Term) (b : SmtTerm), vs ≠ Term.__eo_List_nil →
      __smtx_typeof (__eo_to_smt_exists vs b) ≠ SmtType.None → __smtx_typeof b = SmtType.Bool := by
  intro vs b
  induction vs, b using __eo_to_smt_exists.induct with
  | case1 F => intro h; exact absurd rfl h
  | case2 s T vs F ih =>
    intro _ h
    simp only [__eo_to_smt_exists, __smtx_typeof, native_ite, native_Teq] at h
    have hb : __smtx_typeof (__eo_to_smt_exists vs F) = SmtType.Bool := by
      by_contra hne; exact h (by simp [hne])
    by_cases hv : vs = Term.__eo_List_nil
    · subst hv; simpa only [__eo_to_smt_exists] using hb
    · exact ih hv (by rw [hb]; simp)
  | case3 vs F h1 h2 =>
    intro _ h
    rw [__eo_to_smt_exists.eq_3 _ _ h1 h2] at h
    exact absurd (by rw [__smtx_typeof.eq_def]) h

/-! ## Quantifiers -/

/-- A quantifier: `forall` or `exists`. -/
def IsQuant (op : UserOp) : Prop := op = UserOp.forall ∨ op = UserOp.exists

/-- The translation of a quantifier, with variables. -/
theorem eo_to_smt_quant {op : UserOp} (hop : IsQuant op) (X B : Term)
    (hX : X ≠ Term.__eo_List_nil) :
    __eo_to_smt (eoApp2 op X B) =
      if op = UserOp.forall then SmtTerm.not (__eo_to_smt_exists X (SmtTerm.not (__eo_to_smt B)))
      else __eo_to_smt_exists X (__eo_to_smt B) := by
  rcases hop with rfl | rfl <;> simp [eoApp2, __eo_to_smt, hX]

/-- A quantifier without variables has no translation. -/
theorem eo_to_smt_quant_nil {op : UserOp} (hop : IsQuant op) (B : Term) :
    __eo_to_smt (eoApp2 op Term.__eo_List_nil B) = SmtTerm.None := by
  rcases hop with rfl | rfl <;> simp [eoApp2, __eo_to_smt]

theorem typeof_not_bool' {a : SmtTerm} (h : __smtx_typeof (SmtTerm.not a) ≠ SmtType.None) :
    __smtx_typeof a = SmtType.Bool := by
  simp only [__smtx_typeof, native_ite, native_Teq] at h
  by_contra hne; exact h (by simp [hne])

/-- The body of a well-typed quantifier is Boolean. -/
theorem quant_body_bool {op : UserOp} (hop : IsQuant op) {X B : Term}
    (ht : HasSmtType (eoApp2 op X B)) : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
  by_cases hX : X = Term.__eo_List_nil
  · subst hX; unfold HasSmtType at ht; rw [eo_to_smt_quant_nil hop] at ht
    exact absurd (by rw [__smtx_typeof.eq_def]) ht
  unfold HasSmtType at ht
  rw [eo_to_smt_quant hop X B hX] at ht
  split at ht
  · exact typeof_not_bool' (by
      rw [exists_chain_body_bool X _ hX (by
        rw [typeof_not_bool' ht]; simp)]; simp)
  · exact exists_chain_body_bool X _ hX ht

theorem valueRel_bool' {a b : Bool} (h : SmtValueRel (SmtValue.Boolean a) (SmtValue.Boolean b)) :
    a = b := by
  unfold SmtValueRel __smtx_model_eval_eq at h
  simp only [SmtValue.Boolean.injEq, native_veq] at h
  simpa using h

variable [LogosFacts]

/-- Booleans related under a condition are equal in its models. -/
theorem condEquiv_eval_eq {Φ : SmtModel → Prop} {a b : Term} (h : CondEquiv Φ a b)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Bool) :
    ∀ N, model_wf N → Φ N → __smtx_model_eval N (__eo_to_smt a) = __smtx_model_eval N (__eo_to_smt b) := by
  intro N hN hΦN
  have hb : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := h.type_eq ▸ ha
  obtain ⟨x, hx⟩ := LogosFacts.eval_bool N _ hN ha
  obtain ⟨y, hy⟩ := LogosFacts.eval_bool N _ hN hb
  have hr := (trueIn_mkEq_iff N a b).1 (h.2 N hN hΦN)
  rw [hx, hy] at hr ⊢
  rw [valueRel_bool' hr]

/-- **Congruence under a quantifier** under a stable condition: bodies related
under the condition give quantifiers related under it. -/
theorem condEquiv_quant {Φ : SmtModel → Prop} (hΦ : StableCond Φ) {op : UserOp} (hop : IsQuant op)
    {X B B' : Term} (hB : CondEquiv Φ B B') (ht : HasSmtType (eoApp2 op X B)) :
    CondEquiv Φ (eoApp2 op X B) (eoApp2 op X B') := by
  have hbool := quant_body_bool hop ht
  have heval := condEquiv_eval_eq hB hbool
  by_cases hX : X = Term.__eo_List_nil
  · subst hX; unfold HasSmtType at ht; rw [eo_to_smt_quant_nil hop] at ht
    exact absurd (by rw [__smtx_typeof.eq_def]) ht
  have hT : __smtx_typeof (__eo_to_smt B) = __smtx_typeof (__eo_to_smt B') := hB.type_eq
  refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨ht, ?_⟩, fun M hM hΦM => (trueIn_mkEq_iff M _ _).2 ?_⟩
  · rw [eo_to_smt_quant hop X B hX, eo_to_smt_quant hop X B' hX]
    split
    · have e1 : __smtx_typeof (SmtTerm.not (__eo_to_smt B)) =
          __smtx_typeof (SmtTerm.not (__eo_to_smt B')) := by simp only [__smtx_typeof, hT]
      have e2 := typeof_exists_chain X _ _ e1
      simp only [__smtx_typeof, e2]
    · exact typeof_exists_chain X _ _ hT
  · rw [eo_to_smt_quant hop X B hX, eo_to_smt_quant hop X B' hX]
    have e : __smtx_model_eval M (if op = UserOp.forall then
          SmtTerm.not (__eo_to_smt_exists X (SmtTerm.not (__eo_to_smt B)))
        else __eo_to_smt_exists X (__eo_to_smt B)) =
        __smtx_model_eval M (if op = UserOp.forall then
          SmtTerm.not (__eo_to_smt_exists X (SmtTerm.not (__eo_to_smt B')))
        else __eo_to_smt_exists X (__eo_to_smt B')) := by
      split
      · have e1 : ∀ N, model_wf N → Φ N → __smtx_model_eval N (SmtTerm.not (__eo_to_smt B)) =
            __smtx_model_eval N (SmtTerm.not (__eo_to_smt B')) := fun N hN hΦN => by
          simp only [__smtx_model_eval, heval N hN hΦN]
        have e2 := exists_chain_congr hΦ X _ _ e1 M hM hΦM
        simp only [__smtx_model_eval, e2]
      · exact exists_chain_congr hΦ X _ _ heval M hM hΦM
    rw [e]
    exact LogosFacts.value_rel_refl _

end Telos
