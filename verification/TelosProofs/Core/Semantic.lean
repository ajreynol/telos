import TelosProofs.Core.Equiv
import Telos.Core.Semantic

/-!
# Semantically justified steps are equivalences

`SemProc.equiv`: under its side condition, a `Certified.semantic` step relates
equivalent nodes (`Telos/Core/Semantic.lean`). One case per procedure.

`reorg`: a conjunction whose conjunctions have at least two conjuncts has type
`Bool` iff each of its conjuncts (`Node.conjuncts`) has, and is then true in a
model iff each conjunct is. So two such conjunctions with the same conjuncts
are equivalent.
-/

open Eo Smtm SmtEval

namespace Telos

/-- The CPC conjunction of a list, ending in `true`. -/
abbrev andChain (xs : List Term) : Term := eoRightAssocNil UserOp.and (Term.Boolean true) xs

theorem toSmt_andChain_cons (x : Term) (xs : List Term) :
    __eo_to_smt (andChain (x :: xs)) = SmtTerm.and (__eo_to_smt x) (__eo_to_smt (andChain xs)) := rfl

theorem toSmt_andChain_nil : __eo_to_smt (andChain []) = SmtTerm.Boolean true := rfl

theorem typeof_and_bool (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.and a b) = SmtType.Bool ↔
      __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]
  simp only [native_ite, native_Teq]
  by_cases ha : __smtx_typeof a = SmtType.Bool <;> by_cases hb : __smtx_typeof b = SmtType.Bool <;>
    simp [ha, hb]

theorem typeof_and_cases (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.and a b) = SmtType.Bool ∨ __smtx_typeof (SmtTerm.and a b) = SmtType.None := by
  rw [__smtx_typeof.eq_def]
  simp only [native_ite, native_Teq]
  by_cases ha : __smtx_typeof a = SmtType.Bool <;> by_cases hb : __smtx_typeof b = SmtType.Bool <;>
    simp [ha, hb]

theorem eval_and (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.and a b) =
      __smtx_model_eval_and (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

theorem typeof_true : __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]

theorem eval_true (M : SmtModel) : __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true := by
  rw [__smtx_model_eval.eq_def]

/-- A chain is `Bool` iff its elements are. -/
theorem typeof_andChain (xs : List Term) :
    __smtx_typeof (__eo_to_smt (andChain xs)) = SmtType.Bool ↔
      ∀ x ∈ xs, __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
  induction xs with
  | nil => simp [toSmt_andChain_nil, typeof_true]
  | cons x xs ih => rw [toSmt_andChain_cons, typeof_and_bool, ih]; simp

variable [LogosFacts]

/-- A `Bool` chain is true iff its elements are. -/
theorem eval_andChain (M : SmtModel) (hM : model_wf M) (xs : List Term)
    (h : ∀ x ∈ xs, __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __smtx_model_eval M (__eo_to_smt (andChain xs)) = SmtValue.Boolean true ↔
      ∀ x ∈ xs, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean true := by
  induction xs with
  | nil => simp [toSmt_andChain_nil, eval_true]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih := ih fun y hy => h y (by simp [hy])
    obtain ⟨b, hb⟩ := LogosFacts.eval_bool M _ hM hx
    obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM ((typeof_andChain xs).2 fun y hy => h y (by simp [hy]))
    rw [toSmt_andChain_cons, eval_and, hb, hc]
    have ih' : c = true ↔ ∀ y ∈ xs, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean true := by
      rw [← ih, hc]; simp
    simp only [__smtx_model_eval_and, native_and, SmtValue.Boolean.injEq, Bool.and_eq_true,
      List.mem_cons, forall_eq_or_imp, hb, ← ih']

omit [LogosFacts] in
/-- The translation of a conjunction node with at least two conjuncts. -/
theorem toEo_and (cs : Array Node) (h : 2 ≤ cs.size) :
    (Node.app (.kind .AND) cs).toEo = andChain (cs.toList.map Node.toEo) := by
  rw [Node.toEo_app]
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval, h]

omit [LogosFacts] in
theorem conjuncts_and (cs : Array Node) :
    (Node.app (.kind .AND) cs).conjuncts = cs.toList.flatMap Node.conjuncts := by
  rw [Node.conjuncts]; simp

omit [LogosFacts] in
theorem conjuncts_true : (Node.const (.boolean true)).conjuncts = [] := by
  rw [Node.conjuncts]

omit [LogosFacts] in
theorem conjuncts_other (t : Node) (hA : ∀ cs, t ≠ .app (.kind .AND) cs)
    (hT : t ≠ .const (.boolean true)) : t.conjuncts = [t] := by
  rw [Node.conjuncts.eq_def]
  split
  · exact absurd rfl (hA _)
  · exact absurd rfl hT
  · rfl

omit [LogosFacts] in
theorem andShapeOk_and (cs : Array Node) (h : (Node.app (.kind .AND) cs).andShapeOk = true) :
    2 ≤ cs.size ∧ ∀ c ∈ cs, c.andShapeOk = true := by
  rw [Node.andShapeOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
  refine ⟨h.1, fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
  have := h.2 i (by simpa using hi)
  simp only [Array.getElem_attach] at this
  exact this

omit [LogosFacts] in
theorem smtType_true : (Node.const (.boolean true)).smtType = SmtType.Bool := by
  simp [Node.smtType, Node.toSmt, Node.toEo, Const.toEo]; exact typeof_true

/-- Conjunctions: the type and the truth of a node with `andShapeOk` are those
of its conjuncts. -/
theorem conjuncts_sem (t : Node) (hs : t.andShapeOk = true) :
    (t.smtType = SmtType.Bool ↔ ∀ c ∈ t.conjuncts, c.smtType = SmtType.Bool) ∧
    (t.smtType = SmtType.Bool → ∀ M, model_wf M →
      (__smtx_model_eval M t.toSmt = SmtValue.Boolean true ↔
        ∀ c ∈ t.conjuncts, __smtx_model_eval M c.toSmt = SmtValue.Boolean true)) := by
  by_cases hA : ∃ cs, t = .app (.kind .AND) cs
  · obtain ⟨cs, rfl⟩ := hA
    obtain ⟨hsz, hch⟩ := andShapeOk_and cs hs
    have ih : ∀ c ∈ cs.toList,
        (c.smtType = SmtType.Bool ↔ ∀ d ∈ c.conjuncts, d.smtType = SmtType.Bool) ∧
        (c.smtType = SmtType.Bool → ∀ M, model_wf M →
          (__smtx_model_eval M c.toSmt = SmtValue.Boolean true ↔
            ∀ d ∈ c.conjuncts, __smtx_model_eval M d.toSmt = SmtValue.Boolean true)) :=
      fun c hc => conjuncts_sem c (hch c (Array.mem_toList_iff.1 hc))
    have hty : (Node.app (.kind .AND) cs).smtType = SmtType.Bool ↔
        ∀ c ∈ cs.toList, c.smtType = SmtType.Bool := by
      unfold Node.smtType Node.toSmt
      rw [toEo_and cs hsz, typeof_andChain]
      simp
    refine ⟨?_, ?_⟩
    · rw [hty, conjuncts_and]
      simp only [List.mem_flatMap]
      exact ⟨fun h d ⟨c, hc, hd⟩ => ((ih c hc).1.1 (h c hc)) d hd,
        fun h c hc => (ih c hc).1.2 fun d hd => h d ⟨c, hc, hd⟩⟩
    · intro hb M hM
      have hcb := hty.1 hb
      unfold Node.toSmt
      rw [toEo_and cs hsz, eval_andChain M hM _ (by
        intro x hx; simp only [List.mem_map] at hx; obtain ⟨c, hc, rfl⟩ := hx; exact hcb c hc),
        conjuncts_and]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        List.mem_flatMap]
      exact ⟨fun h d c hc hd => ((ih c hc).2 (hcb c hc) M hM).1 (h c hc) d hd,
        fun h c hc => ((ih c hc).2 (hcb c hc) M hM).2 fun d hd => h d c hc hd⟩
  · by_cases hT : t = .const (.boolean true)
    · subst hT
      refine ⟨by simp [conjuncts_true, smtType_true], fun _ M _ => ?_⟩
      simp only [conjuncts_true, List.not_mem_nil, false_imp_iff, implies_true, iff_true]
      simp [Node.toSmt, Node.toEo, Const.toEo]
      exact eval_true M
    · have h := conjuncts_other t (fun cs e => hA ⟨cs, e⟩) hT
      simp [h]
termination_by sizeOf t
decreasing_by
  have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.1 ‹_›); simp_all; omega

omit [LogosFacts] in
/-- A conjunction that translates has type `Bool`. -/
theorem and_smtType_bool (cs : Array Node) (h : (Node.app (.kind .AND) cs).WellTyped) :
    (Node.app (.kind .AND) cs).smtType = SmtType.Bool := by
  by_cases hsz : 2 ≤ cs.size
  · unfold Node.WellTyped Node.smtType Node.toSmt at *
    rw [toEo_and cs hsz] at *
    cases hcs : cs.toList.map Node.toEo with
    | nil =>
      have := congrArg List.length hcs
      rw [List.length_map, Array.length_toList, List.length_nil] at this
      omega
    | cons x xs =>
      rw [hcs, toSmt_andChain_cons] at h
      rw [toSmt_andChain_cons]
      exact (typeof_and_cases _ _).resolve_right h
  · exfalso
    apply h
    unfold Node.smtType Node.toSmt
    rw [Node.toEo_app]
    simp [Op.eoShape, Kind.eoShape, AppShape.toEo, hsz]
    rfl

/-- **Semantically justified steps are equivalences.** -/
theorem SemProc.equiv : ∀ (p : SemProc) (n m : Node), p.Ok n m → n.WellTyped → n.Equiv m
  | .reorg, n, m, ⟨hkn, _, hsn, hsm, hmn, hnm⟩, hn => by
    have hnb : n.smtType = SmtType.Bool := by
      match n, hkn with
      | .app (.kind .AND) cs, _ => exact and_smtType_bool cs hn
    have ⟨hn₁, hn₂⟩ := conjuncts_sem n hsn
    have ⟨hm₁, hm₂⟩ := conjuncts_sem m hsm
    have hmb : m.smtType = SmtType.Bool := hm₁.2 fun c hc => hn₁.1 hnb c (hmn c hc)
    refine (Node.equiv_iff n m).2 ⟨hn, ?_, fun M hM => ?_⟩
    · exact hnb.trans hmb.symm
    · obtain ⟨b, hb⟩ := LogosFacts.eval_bool M _ hM hnb
      obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hmb
      have e₁ := hn₂ hnb M hM
      have e₂ := hm₂ hmb M hM
      rw [hb, SmtValue.Boolean.injEq] at e₁
      rw [hc, SmtValue.Boolean.injEq] at e₂
      have hiff : b = true ↔ c = true := by
        rw [e₁, e₂]
        exact ⟨fun h d hd => h d (hmn d hd), fun h d hd => h d (hnm d hd)⟩
      have : b = c := by cases b <;> cases c <;> simp_all
      rw [hb, hc, this]
      exact LogosFacts.value_rel_refl _

end Telos
