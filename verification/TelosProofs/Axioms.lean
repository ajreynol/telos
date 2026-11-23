import TelosProofs.Rewriter.Rewriter
import TelosProofs.Preprocess.Preprocess
import TelosProofs.Solver.Model
import TelosProofs.Solver.Frontend
import TelosProofs.Solver.Correct

/-!
# Axiom audit

Fails the build if a main theorem depends on anything other than

* Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`, and
* the auxiliary axioms that `native_decide` creates (names containing
  `native_decide`). Each asserts that a decision procedure, run by Lean's compiled
  code, returned `true`, so they trust the Lean compiler. They enter through
  Logos's proofs, which use `native_decide` (see `TRUSTED.md`).

In particular, `sorryAx` and any other postulated constant fail the build.
-/

open Lean Elab Command in
/-- `#assert_axioms c` fails unless `c` uses only the axioms allowed above. -/
elab "#assert_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let allowed (a : Name) : Bool :=
    standard.contains a || a.components.any (· == `native_decide)
  let bad := axioms.filter (!allowed ·)
  unless bad.isEmpty do
    throwError "'{name}' depends on disallowed axioms: {bad.toList}"
  let native := (axioms.filter (!standard.contains ·)).size
  logInfo m!"'{name}': standard axioms, plus {native} native_decide axioms from Logos"

-- The default build checks the theorems that take Logos's checker soundness as a
-- hypothesis; `TelosFull/Main.lean` checks the unconditional `rewrite_correct`
-- and `preprocess_correct`.
#assert_axioms Telos.rewrite_correct_of_logos
#assert_axioms Telos.preprocess_correct_of_logos
#assert_axioms Telos.Frontend.solveScript_unsat
#assert_axioms Telos.Frontend.solve_unsat
#assert_axioms Telos.Frontend.solve_sat
#assert_axioms Telos.Solver.EE.explainLitV_sound
#assert_axioms Telos.Solver.run_unsat_sound
#assert_axioms Telos.Frontend.solveScript_sat
#assert_axioms Telos.Solver.satisfies_sound
