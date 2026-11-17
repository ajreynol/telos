import TelosProofs.PolyNorm
import TelosProofs.LogosFacts

/-!
# Statically justified arithmetic normalization

`StaticProc.arithNorm` rewrites `n` to `arithNorm n` without running Logos's
checker. This file justifies it: under `ArithNormOk`, the one-step command list
`[arith_poly_norm (= n (arithNorm n))]` meets the hypotheses of Logos's
`proven_from_empty_valid` (`arithNorm_provesEq`), so `Certified.equiv` covers the
step like any checked one, and the printed proof contains exactly that step.
Likewise for `StaticProc.arithRel`: under `ArithRelOk`, the two-step list whose
premise is an `arith_poly_norm` step meets them (`arithRel_provesEq`).
-/

open Eo Smtm

namespace Telos

open Arith

variable [LogosFacts]

theorem arithNorm_provesEq {n : Node} (h : ArithNormOk n (polyOf n) (arithNorm n)) :
    ProvesEq (StaticProc.arithNormCmds n) n (arithNorm n) := by
  apply PolyNorm.arithNorm_provesEq_of_typeof h
  exact LogosFacts.eo_typeof_bool _ h.2.1

/-- The Eunoia type of a well-typed equation of nodes is `Bool`. -/
theorem eo_typeof_eqFormula {a b : Node} (h : __smtx_typeof (__eo_to_smt (eqFormula a b)) = SmtType.Bool) :
    __eo_typeof (eqFormula a b) = Term.Bool :=
  LogosFacts.eo_typeof_bool _ h

theorem arithRel_provesEq {n m a b : Node} (h : ArithRelOk n m a b) :
    ProvesEq (StaticProc.arithRelCmds n m a b) n m :=
  PolyNorm.arithRel_provesEq_of_typeof h (eo_typeof_eqFormula h.2.1) (eo_typeof_eqFormula h.2.2.2.1)

end Telos
