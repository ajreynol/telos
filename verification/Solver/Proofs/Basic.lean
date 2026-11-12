import Solver
import Cpc.Spec

/-!
# Proofs (M0 placeholder)

Smoke test that the proof side sees both the solver and Logos's verification
library. Obligations that need `SmtModel` or Logos rule proofs go under
`Solver/Proofs/`.
-/

open Eo

namespace Solver.Proofs

example : resolutionRule = CRule.resolution := rfl

example : Term → Bool → Prop := eo_satisfiability

end Solver.Proofs
