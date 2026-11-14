import Std.Data.HashMap
import Telos.Rules.Generated
import Telos.Rules.Match

/-!
# The rule database

Lookup of the generated rules by their Eunoia name, for the theory strategies.
-/

namespace Telos

/-- The generated rules, by Eunoia name. -/
def ruleTable : Std.HashMap String RuleSpec :=
  generatedRules.foldl (init := {}) fun m r => if m.contains r.name then m else m.insert r.name r

/-- The generated rule with this Eunoia name. -/
def findRule? (name : String) : Option RuleSpec :=
  ruleTable.get? name

/-- Rewrite `n` by the named CPC rule, if it applies. -/
def rewriteBy (name : String) (n : Node) : Option (Rw n) :=
  (findRule? name).bind (·.apply n)

end Telos
