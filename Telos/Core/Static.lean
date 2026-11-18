import Telos.Core.PolyNorm

/-!
# Statically justified steps

A `Certified.static p` step rewrites `n` to `m` without running Logos's checker.
`p : StaticProc` names the procedure. For each procedure:

* `p.Ok n m` is its side condition, cheap to decide; the theory rewriter decides
  it (or builds it by construction) before taking the step;
* `p.cmds n m` is the CPC command list the step stands for. It is not run; proof
  output prints it;
* `verification/TelosProofs/Core/Static.lean` proves
  `p.Ok n m → ProvesEq (p.cmds n m) n m` (`StaticProc.provesEq`), so
  `Certified.equiv` covers the step, and the printed commands are accepted.

To add a procedure: a constructor here with its `Ok` and `cmds` cases, its code
in a module below `Telos.Core.Certified` (as `Telos/Core/PolyNorm.lean`),
and its case of `StaticProc.provesEq`. Nothing else changes: the driver, the
proof printer and `Certified.equiv` handle every procedure alike.
-/

open Eo

namespace Telos

/-- The statically justified procedures. -/
inductive StaticProc where
  /-- `n` to its arithmetic normal form `arithNorm n`, by `arith_poly_norm`. -/
  | arithNorm
  /-- `n` to `m` by `arith_poly_norm_rel`, from the premise `(= a b)`, itself an
  `arith_poly_norm` step. -/
  | arithRel (a b : Node)

/-- `[arith_poly_norm (= n (arithNorm n))]`. -/
def StaticProc.arithNormCmds (n : Node) : CCmdList :=
  .cons (.step .arith_poly_norm (.cons (eqFormula n (Arith.arithNorm n)) .nil) .nil) .nil

/-- `[arith_poly_norm (= a b), arith_poly_norm_rel (= n m) from it]`. -/
def StaticProc.arithRelCmds (n m a b : Node) : CCmdList :=
  .cons (.step .arith_poly_norm (.cons (eqFormula a b) .nil) .nil)
    (.cons (.step .arith_poly_norm_rel (.cons (eqFormula n m) .nil) (.cons 0 .nil)) .nil)

/-- The side condition of a step from `n` to `m`. -/
def StaticProc.Ok : StaticProc → Node → Node → Prop
  | .arithNorm, n, m => m = Arith.arithNorm n ∧ Arith.ArithNormOk n (Arith.polyOf n) (Arith.arithNorm n)
  | .arithRel a b, n, m => Arith.ArithRelOk n m a b

/-- The CPC commands a step from `n` to `m` stands for. -/
def StaticProc.cmds : StaticProc → Node → Node → CCmdList
  | .arithNorm, n, _ => StaticProc.arithNormCmds n
  | .arithRel a b, n, m => StaticProc.arithRelCmds n m a b

end Telos
