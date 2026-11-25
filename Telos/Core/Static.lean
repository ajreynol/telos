import Telos.Core.PolyNorm
import Telos.Core.Template
import Telos.Core.AciNorm
import Telos.Core.LenConcat

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
  /-- `n` to its arithmetic normal form `arithNorm n o`, by `arith_poly_norm`,
  with its monomials in the order `o`. -/
  | arithNorm (o : NodeOrder)
  /-- `n` to `m` by `arith_poly_norm_rel`, from the premise `(= a b)`, itself an
  `arith_poly_norm` step. -/
  | arithRel (a b : Node)
  /-- `n` to `m` by the template rule `r` with the arguments `args`
  (`Telos/Core/Template.lean`), read right to left with `rev`. -/
  | template (r : TRule) (args : List Node) (rev : Bool)
  /-- A conjunction or disjunction `n` to `m`, with the same operands, by
  `aci_norm` (`Telos/Core/AciNorm.lean`). -/
  | aci
  /-- A concatenation of strings `n` to `m`, with the same components in order, by
  `aci_norm` (`Telos/Core/AciNorm.lean`). -/
  | aciConcat
  /-- The length of `(str.++ a b cs…)`, by `str_len_concat_rec`
  (`Telos/Core/LenConcat.lean`). -/
  | lenConcat (a b : Node) (cs : List Node)

/-- `[arith_poly_norm (= n (arithNorm n o))]`. -/
def StaticProc.arithNormCmds (n : Node) (o : NodeOrder := {}) : CCmdList :=
  .cons (.step .arith_poly_norm (.cons (eqFormula n (Arith.arithNorm n o)) .nil) .nil) .nil

/-- `[arith_poly_norm (= a b), arith_poly_norm_rel (= n m) from it]`. -/
def StaticProc.arithRelCmds (n m a b : Node) : CCmdList :=
  .cons (.step .arith_poly_norm (.cons (eqFormula a b) .nil) .nil)
    (.cons (.step .arith_poly_norm_rel (.cons (eqFormula n m) .nil) (.cons 0 .nil)) .nil)

/-- `[aci_norm (= n m)]`. -/
def StaticProc.aciCmds (n m : Node) : CCmdList :=
  .cons (.step .aci_norm (.cons (eqFormula n m) .nil) .nil) .nil

/-- The side condition of a step from `n` to `m`. -/
def StaticProc.Ok : StaticProc → Node → Node → Prop
  | .arithNorm o, n, m => m = Arith.arithNorm n o ∧ Arith.ArithNormOk n (Arith.polyOf n) (Arith.arithNorm n o)
  | .arithRel a b, n, m => Arith.ArithRelOk n m a b
  | .template r args rev, n, m => if rev then r.Ok args m n else r.Ok args n m
  | .aci, n, m => Aci.Ok n m
  | .aciConcat, n, m => AciConcat.Ok n m
  | .lenConcat a b cs, n, m => LenConcat.Ok a b cs n m

/-- The CPC commands a step from `n` to `m` stands for. -/
def StaticProc.cmds : StaticProc → Node → Node → CCmdList
  | .arithNorm o, n, _ => StaticProc.arithNormCmds n o
  | .arithRel a b, n, m => StaticProc.arithRelCmds n m a b
  | .template r args rev, _, _ => r.cmds args rev
  | .aci, n, m => StaticProc.aciCmds n m
  | .aciConcat, n, m => StaticProc.aciCmds n m
  | .lenConcat a b cs, _, _ => LenConcat.cmds a b cs

end Telos
