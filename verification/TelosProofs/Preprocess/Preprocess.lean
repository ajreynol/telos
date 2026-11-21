import TelosProofs.Core.Certified
import Telos.Preprocess.Preprocess

/-!
# Correctness of the preprocessor

The preprocessor keeps cvc5's assertion pipeline as one node, the conjunction of
the assertions, and every pass is a certified rewrite of it
(`Telos/Preprocess/Pipeline.lean`). So the theorem that every certified rewrite
yields an equivalent node (`Certified.equiv`) gives, at once, that the
preprocessed assertions mean what the input ones mean: their conjunction
`(preprocessCert as).1` (the conjunction of `preprocess as`, or `false`) is
equivalent to `inputNode as`, the conjunction of the input assertions and `true`,
whatever the options (`PPOptions`: cvc5's, with the defaults of the logic).
In particular the input is satisfiable iff the output is, in the same models.
-/

namespace Telos

open Preprocess

/-- **Correctness of the preprocessor**, given the Logos theorems it uses
(`LogosFacts`). -/
theorem preprocess_correct_of_logos [LogosFacts] (as : List Node)
    (h : (inputNode as).WellTyped) (opts : PPOptions := {}) (o : NodeOrder := {}) :
    (inputNode as).Equiv (preprocessCert as opts o).1 :=
  Certified.equiv (preprocessCert as opts o).2 h

end Telos
