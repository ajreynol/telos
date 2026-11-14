import TelosProofs.PolyNorm
import Cpc.Proofs.RuleSupport.SubstituteTypeSupport

/-!
# Statically justified arithmetic normalization

`Certified.arithNorm` rewrites `n` to `arithNorm n` without running Logos's
checker. This file justifies it: under `ArithNormOk`, the one-step command list
`[arith_poly_norm (= n (arithNorm n))]` meets the hypotheses of Logos's
`proven_from_empty_valid` (`arithNorm_provesEq`), so `Certified.equiv` covers the
step like any checked one, and the printed proof contains exactly that step.
-/

open Eo Smtm

namespace Telos

open Arith

theorem arithNorm_provesEq {n : Node} (h : ArithNormOk n (polyOf n) (arithNorm n)) :
    ProvesEq (Certified.arithNormCmds n) n (arithNorm n) := by
  apply PolyNorm.arithNorm_provesEq_of_typeof h
  have hBool : __smtx_typeof (__eo_to_smt (eqFormula n (arithNorm n))) = SmtType.Bool := h.2.1
  apply SubstituteSupport.eo_typeof_eq_of_smt_type_eq _ _
  · show __smtx_typeof (__eo_to_smt (eqFormula n (arithNorm n))) ≠ SmtType.None
    rw [hBool]; simp
  · simp [__eo_to_smt_type, __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec, SmtEval.native_and]
  · rw [hBool]; rfl

end Telos
