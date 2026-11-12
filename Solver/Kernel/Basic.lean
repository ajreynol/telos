import Cpc.Logos

/-!
# Kernel (M0 placeholder)

Smoke test that the solver can see Logos's generated checker definitions.
`Mode`, `Derived`, `Provable` and the rule combinators (plan §2, M1) go here.
-/

open Eo

namespace Solver

/-- The CPC rule the CDCL core will use to justify learned clauses. -/
def resolutionRule : CRule := CRule.resolution

end Solver
