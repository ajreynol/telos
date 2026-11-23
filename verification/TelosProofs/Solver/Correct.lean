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
  obtain ⟨M, hM, hv⟩ := solveScript_sat sc u false true false true vs false false hs ha hin
  exact ⟨as, ppInput_assertions hin, smt_satisfiability.intro_true _ ⟨M, hM, hv⟩⟩

end Frontend

end Telos
