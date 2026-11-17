import Cpc.Proofs.Common
import Cpc.TranslationChecks

/-!
# The Logos theorem telos builds on

telos's proofs use one theorem of Logos's checker soundness proof:
`proven_from_empty_valid` (`Cpc/Proofs/ProvenFromEmpty.lean`). A command list run
from the empty checker state proves facts that are well typed and true in every
well-formed model. Its proof covers every CPC rule and is most of Logos's proof
code.

So that telos's proofs can be checked without building it, the theorem is
restated here as a proposition, `LogosCheckerSound`, and taken as a hypothesis
(`Telos.rewrite_correct_of_logos`). This file needs only definitions, so the
default build stays cheap. `TelosFull/` (`lake build TelosFull`) proves
`LogosCheckerSound` from `proven_from_empty_valid`, which keeps this statement
in sync with Logos, and derives the unconditional `Telos.rewrite_correct`.
-/

open Eo
open Smtm

namespace Telos

/-- Logos's `proven_from_empty_valid`, as a proposition. -/
def LogosCheckerSound : Prop :=
  ∀ (cs : CCmdList) (P : Term),
    CmdListTranslationOk cs →
    __eo_state_is_closed (__eo_invoke_cmd_list CState.nil cs) = true →
    __eo_state_proven_nth (__eo_invoke_cmd_list CState.nil cs) 0 = P →
    RuleProofs.eo_has_bool_type P ∧ ∀ M, model_wf M → eo_interprets M P true

end Telos
