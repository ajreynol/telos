import TelosProofs.ArithNorm

/-!
# Statically justified steps are CPC steps

`StaticProc.provesEq`: under its side condition, the commands a static step
stands for are accepted by Logos's checker (`Telos/Rewriter/Static.lean`). One
case per procedure; `Certified.equiv` uses it for every `Certified.static` step.
-/

namespace Telos

theorem StaticProc.provesEq : ∀ (p : StaticProc) (n m : Node), p.Ok n m → ProvesEq (p.cmds n m) n m
  | .arithNorm, n, _, ⟨rfl, h⟩ => arithNorm_provesEq h
  | .arithRel _ _, _, _, h => arithRel_provesEq h

end Telos
