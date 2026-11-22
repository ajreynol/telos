import TelosProofs.Core.ArithNorm
import TelosProofs.Core.Template

/-!
# Statically justified steps are CPC steps

`StaticProc.provesEq`: under its side condition, the commands a static step
stands for are accepted by Logos's checker (`Telos/Core/Static.lean`). One
case per procedure; `Certified.equiv` uses it for every `Certified.static` step.
-/

namespace Telos

variable [LogosFacts] in
theorem StaticProc.provesEq : ∀ (p : StaticProc) (n m : Node), p.Ok n m → ProvesEq (p.cmds n m) n m
  | .arithNorm _, n, _, ⟨rfl, h⟩ => arithNorm_provesEq h
  | .arithRel _ _, _, _, h => arithRel_provesEq h
  | .template _ _ false, _, _, h => TRule.provesEq h
  | .template _ _ true, _, _, h => TRule.provesEq_rev h

end Telos
