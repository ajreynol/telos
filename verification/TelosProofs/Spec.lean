import Telos.Node.ToEo
import Cpc.Spec

/-!
# Specification: equivalence of nodes

Two nodes are equivalent when the CPC formula `(= t s)` over their translations is
**well typed** and **valid**, i.e. `(not (= t s))` is unsatisfiable in Logos's
semantics (`eo_satisfiability … false`).

The typing conjunct is needed. Logos evaluates `=` to a Boolean even on
`NotValue` (`__smtx_model_eval_eq`), so unsatisfiability of `(not (= t s))` alone
holds vacuously when both sides are ill typed. With the typing conjunct, `Equiv t s`
implies that `t` and `s` are well typed, have the same type, and have the same
value in every well-formed model.

This is exactly the meaning of a CPC step concluding `(= t s)`, which is what lets
rewrites be justified by CPC proofs later.
-/

open Eo
open Smtm

namespace Telos

-- `eqFormula t s` is the CPC formula `(= t s)` (`Telos/Node/ToEo.lean`).

/-- `t` and `s` are equivalent: `(= t s)` is well typed and valid. -/
def Node.Equiv (t s : Node) : Prop :=
  __smtx_typeof (__eo_to_smt (eqFormula t s)) = SmtType.Bool ∧
  eo_satisfiability (eoApp1 UserOp.not (eqFormula t s)) false

end Telos
