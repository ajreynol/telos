import TelosProofs.Solver.Frontend
import TelosProofs.Solver.Model

/-!
# The solver's answers, in Logos's semantics

The statements of the solver's correctness, in Logos's own notion of
satisfiability, `eo_satisfiability t b` (`Cpc/Spec.lean`), for the input of a
script: the conjunction of its assertions, as a Logos term by telos's
translation. The input's meaning is the composition of
1. the front end: Logos's SMT-LIB parser, then telos's reading of the script's
   assertions as nodes (`Frontend.inputAssertions`; not verified);
2. telos's translation of nodes to Logos terms (`Node.toEo`, part of the
   specification, `TRUSTED.md`);
3. Logos's semantics: `eo_satisfiability t b` is `smt_satisfiability
   (__eo_to_smt t) b`, Logos's translation of the term to an SMT term, which
   is satisfiable (`b = true`: true in some well-formed model) or
   unsatisfiable (`b = false`: false in every well-formed model).

The theorems take Logos's theorems as the hypothesis `[LogosFacts]`, as the
others of `TelosProofs` do; `TelosFull/Main.lean` discharges it.
-/

open Eo Smtm SmtEval

namespace Telos

namespace Frontend

/-- **Logos's satisfiability of a script**: the conjunction of its assertions
(`Preprocess.inputNode`, with `true`), translated (`Node.toEo`), is
satisfiable (`b = true`) or unsatisfiable (`b = false`) in Logos's semantics
(`eo_satisfiability`). -/
def Script.satisfiability (sc : Script) (b : Bool) : Prop :=
  ∃ as, inputAssertions sc = .ok as ∧ eo_satisfiability (Preprocess.inputNode as).toEo b

end Frontend

set_option linter.unusedSectionVars false

variable [LogosFacts]

namespace Frontend

open Preprocess

/-- The assertions of a script are formulas in Logos's typing. -/
theorem inputAssertions_bool {sc : Script} {as : List Node} (h : inputAssertions sc = .ok as) :
    ∀ a ∈ as, HasBoolType a.toEo := by
  unfold inputAssertions at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i as' _
    split at h
    · rename_i hall
      simp only [Except.ok.injEq] at h
      subst h
      intro a ha
      have := List.all_eq_true.1 hall a ha
      simp only [beq_iff_eq] at this
      unfold HasBoolType
      rw [← this, Node.smtTypeF_eq]
      rfl
    · simp at h

/-- `ppInput` reads the assertions by `inputAssertions`. -/
theorem ppInput_assertions {sc : Script} {u : UserOptions} {opts : PPOptions} {as : List Node}
    (h : ppInput sc u = .ok (opts, as)) : inputAssertions sc = .ok as := by
  unfold ppInput at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i as' has
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact has

/-- The conjunction of formulas is a formula. -/
theorem inputNode_bool {as : List Node} (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    HasBoolType (inputNode as).toEo := by
  have hsize : 2 ≤ (as ++ [Node.mkTrue, Node.mkTrue]).toArray.size := by simp
  have hall : ∀ x ∈ as ++ [Node.mkTrue, Node.mkTrue], HasBoolType x.toEo := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hb x hx
    · exact (good_true (default : SmtModel)).1
    · exact (good_true (default : SmtModel)).1
  unfold inputNode Node.mkNode
  rw [and_bool_iff _ hsize]
  intro i hi
  exact hall _ (by simp)

/-- A model that is accepted is a model of the assertions: it satisfies them, or
their preprocessing, which is equivalent to them. -/
theorem accepts_sound {M : Solver.Model} {as : List Node} {opts : PPOptions} {pp : Bool} {o : NodeOrder}
    (hb : ∀ a ∈ as, HasBoolType a.toEo) (h : accepts M as opts pp o = true) :
    model_wf (Solver.toSmtModel M) ∧ TrueIn (Solver.toSmtModel M) (inputNode as).toEo := by
  unfold accepts at h
  rw [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h⟩
  · exact Solver.satisfies_sound h
  · have hwf := (Solver.satisfies_sound h).1
    refine ⟨hwf, ?_⟩
    have hP := Solver.satisfies_mem h (preprocessCert as opts o).1 (by simp)
    have hIb : HasBoolType (inputNode as).toEo := inputNode_bool hb
    have heq := preprocess_correct_of_logos as (Solver.wellTyped_of_bool hIb) opts o
    obtain ⟨-, -, hval⟩ := (Node.equiv_iff _ _).1 heq
    have hrel := hval _ hwf
    obtain ⟨c, hc⟩ := LogosFacts.eval_bool _ _ hwf hIb
    have hc' : __smtx_model_eval (Solver.toSmtModel M) (inputNode as).toSmt = SmtValue.Boolean c := hc
    rw [hc', hP] at hrel
    have := valueRel_bool hrel
    unfold TrueIn
    show __smtx_model_eval _ (inputNode as).toSmt = _
    rw [hc', this]

/-- **`solveScript`'s `sat` answers are correct**: the assertions are
satisfiable, in the Logos model of the model found. -/
theorem solveScript_sat (sc : Script) (u : UserOptions) (ee pp wp co vs te ev : Bool)
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co vs te ev = .ok (out, r))
    (hs : r.answer = .sat) {opts : PPOptions} {as : List Node}
    (hin : ppInput sc u = .ok (opts, as)) (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
  simp only [solveScript, hin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · -- whichever solved it, the answer is `sat` only if the model satisfies the
    -- input
    have key : ∀ (o : NodeOrder) (r0 : Solver.Result) (w : Solver.Unknown), (if r0.answer != .sat then r0 else
        if accepts (Solver.buildModel r0.ee (Solver.relevantTerms r0.asserted) (Solver.freeConsts as)
            (engineDefs as opts pp o) as r0.arithModel r0.asserted) as opts pp o then
          { r0 with model := some (Solver.buildModel r0.ee (Solver.relevantTerms r0.asserted)
            (Solver.freeConsts as) (engineDefs as opts pp o) as r0.arithModel r0.asserted) }
        else rejectModel r0 w).answer = .sat →
        ∃ M, model_wf M ∧ TrueIn M (inputNode as).toEo := by
      intro _ r0 _ hs
      split at hs
      · rename_i hne
        simp [hs] at hne
      · split at hs
        · rename_i hsat
          exact ⟨_, accepts_sound hb hsat⟩
        · rw [rejectModel_answer] at hs
          cases hs
    split at h
    · try simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact key _ _ _ hs
    · split at h
      · simp at h
      · try simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact key _ _ _ hs

/-- `solve` is `solveScript`'s answer, with no events. -/
theorem solve_ok {sc : Script} {u : UserOptions} {vs : Bool} {a : Solver.Answer}
    (h : solve sc u vs = .ok a) :
    ∃ out r, solveScript sc u (viaSat := vs) (events := false) = .ok (out, r) ∧ r.answer = a := by
  unfold solve solveAnswer at h
  simp only [bind, Except.bind, pure, Except.pure, Except.map] at h
  split at h
  · simp at h
  · rename_i v hv
    simp only [Except.ok.injEq] at h
    split at hv
    · simp at hv
    · rename_i w hw
      simp only [Except.ok.injEq] at hv
      exact ⟨w.1, w.2, hw, by rw [← h, ← hv]⟩

/-- `solveScript` succeeds only once it has read the script. -/
theorem solveScript_ppInput {sc : Script} {u : UserOptions} {ee pp wp co vs te ev : Bool}
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co vs te ev = .ok (out, r)) :
    ∃ opts as, ppInput sc u = .ok (opts, as) := by
  simp only [solveScript, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i v hv
      exact ⟨v.1, v.2, hv⟩

/-- **`unsat` is correct**, in Logos's semantics. -/
theorem solve_unsat {sc : Script} {u : UserOptions} {vs : Bool} (h : solve sc u vs = .ok .unsat) :
    sc.satisfiability false := by
  obtain ⟨out, r, hs, ha⟩ := solve_ok h
  obtain ⟨opts, as, hin⟩ := solveScript_ppInput hs
  have hia := ppInput_assertions hin
  have hb := inputAssertions_bool hia
  refine ⟨as, hia, smt_satisfiability.intro_false _ ?_⟩
  intro M hM
  have hno := solveScript_unsat sc u false true false true vs false false hs ha hin hb M hM
  obtain ⟨b, hv⟩ := LogosFacts.eval_bool M _ hM (inputNode_bool hb)
  cases b
  · exact hv
  · exact absurd hv hno

/-- **`sat` is correct**, in Logos's semantics. -/
theorem solve_sat {sc : Script} {u : UserOptions} {vs : Bool} (h : solve sc u vs = .ok .sat) :
    sc.satisfiability true := by
  obtain ⟨out, r, hs, ha⟩ := solve_ok h
  obtain ⟨opts, as, hin⟩ := solveScript_ppInput hs
  have hb := inputAssertions_bool (ppInput_assertions hin)
  obtain ⟨M, hM, hv⟩ := solveScript_sat sc u false true false true vs false false hs ha hin hb
  exact ⟨as, ppInput_assertions hin, smt_satisfiability.intro_true _ ⟨M, hM, hv⟩⟩

end Frontend

end Telos
