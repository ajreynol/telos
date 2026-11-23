import TelosProofs.Solver.SatProof
import TelosProofs.Solver.Solve

/-!
# `unsat` answers of the front end are correct

`solveScript_unsat`: whichever solved the assertions, the engine alone
(`Solver.run_unsat_sound`) or the SAT solver with it (`runSat_refutes`: its
`unsat` comes with a certificate that checks, `Solver.runSat_unsat`, and so
refutes the formulas, `SatProof.Cert.check_sound`), an `unsat` answer means
that the input assertions are unsatisfiable.
-/

open Eo Smtm SmtEval

namespace Telos

set_option linter.unusedSectionVars false

variable [LogosFacts]

namespace Solver

omit [LogosFacts] in
theorem true_notFalse (M : SmtModel) : TrueIn M (Node.notNode Node.mkFalse).toEo := by
  have hb : SatProof.BoolVal M Node.mkFalse := ⟨false, by
    show __smtx_model_eval M (__eo_to_smt (Node.mkFalse).toEo) = _
    rw [toEo_false]; exact eval_bool_const M false⟩
  refine (SatProof.notNode_sem hb).2.2 ?_
  unfold TrueIn; rw [toEo_false, eval_bool_const]; simp

/-- **An `unsat` of the SAT solver refutes its formulas.** -/
theorem runSat_refutes (c : Config) (fs : List Node) (h : (runSat c fs).answer = .unsat)
    (M : SmtModel) (hM : model_wf M) (hfs : ∀ f ∈ fs, TrueIn M f.toEo) : False := by
  obtain ⟨cert, -, hc⟩ := runSat_unsat c fs h
  refine SatProof.Cert.check_sound hc M hM ?_
  intro f hf
  simp only [certInputs, Array.toList_append, List.mem_append] at hf
  rcases hf with hf | hf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact (Frontend.good_true M).2
    · exact true_notFalse M
  · exact hfs f (by simpa using hf)

end Solver

namespace Frontend

open Preprocess

/-- **Correctness of `unsat`.** If telos answers `unsat` on a script whose
assertions are Boolean, no well-formed model satisfies the input assertions. -/
theorem solveScript_unsat (sc : Script) (u : UserOptions) (ee pp wp co vs te ev : Bool)
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co vs te ev = .ok (out, r))
    (hu : r.answer = .unsat) {opts : PPOptions} {as : List Node}
    (hin : ppInput sc u = .ok (opts, as)) (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    ∀ M, model_wf M → ¬ TrueIn M (inputNode as).toEo := by
  intro M hM hv
  have hout := engineAssertions_sound hM as opts pp (orderFor co sc as) hb hv
  rw [← preprocessed_fst] at hout
  simp only [solveScript, hin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · -- the SAT solver
      try simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      generalize hr : Solver.runSat _ _ = r0 at hu
      have hu' : r0.answer = .unsat := by
        split at hu
        · exact hu
        · split at hu <;> simp_all
      rw [← hr] at hu'
      exact Solver.runSat_refutes _ _ hu' M hM (fun f hf => (hout f hf).2)
    · split at h
      · simp at h
      · rename_i lits hlits
        try simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hgood := literalsOf_sound hM _ [] lits (engineLiterals_ok hlits) (by simp) hout
        -- the check of a `sat` answer turns it into `unknown`, never into `unsat`
        generalize hrs : Solver.runSat _ _ = rs at hu
        generalize hrn : Solver.run _ lits = rn at hu
        repeat' split at hu
        all_goals first
          | (simp at hu; done)
          | (have hu2 : rs.answer = .unsat := by simpa using hu
             rw [← hrs] at hu2
             exact Solver.runSat_refutes _ _ hu2 M hM (fun f hf => (hout f hf).2))
          | (have hu2 : rn.answer = .unsat := by simpa using hu
             rw [← hrn] at hu2
             exact Solver.run_unsat_sound _ lits hu2 (fun l hl => (hgood l hl).1) M hM
               (fun l hl => (hgood l hl).2))

end Frontend

end Telos
