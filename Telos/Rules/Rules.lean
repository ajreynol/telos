import Telos.Rules.Generated
import Telos.Rules.Match

/-!
# The rule database

Lookup of the generated rules by their Eunoia name, for the theory strategies.
-/

namespace Telos

/-- The generated rule with this Eunoia name. -/
def findRule? (name : String) : Option RuleSpec :=
  generatedRules.find? (·.name == name)

/-- Rewrite `n` by the named CPC rule, if it applies. -/
def rewriteBy (name : String) (n : Node) : Option { m // Certified n m } :=
  (findRule? name).bind (·.apply n)

end Telos
