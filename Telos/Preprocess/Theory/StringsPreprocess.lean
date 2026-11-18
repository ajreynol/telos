import Telos.Preprocess.SkolemSteps

/-!
# Strings theory preprocessing

cvc5's `TheoryStrings::ppRewrite` (`src/theory/strings/theory_strings.cpp`), with
the default options (no regular expression elimination, no finite model
finding): `(str.from_code t)` is replaced by its purification skolem `k`, with
its eager reduction as the lemma,
`(ite (and (<= 0 t) (< t 196608)) (= t (str.to_code k)) (= k ""))`
(`string_eager_reduction`). The rest of the hook only checks the input.
-/

namespace Telos.Preprocess

open Node

/-- `TheoryStrings::ppRewrite`. -/
def stringsPpRewrite (n : Node) : Option (Rw n × Option (Rw mkTrue)) := do
  if n.getKind != .STRING_FROM_CODE then none
  return (← purifyStep n, lemmaBy [stepWith .string_eager_reduction [n.toEo]])

end Telos.Preprocess
