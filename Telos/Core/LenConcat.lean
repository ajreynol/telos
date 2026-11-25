import Cpc.Logos
import Telos.Core.Node.SmtTypeFast

/-!
# The length of a concatenation of strings

`str-len-concat-rec` takes `(str.len (str.++ a b c …))` to
`(+ (str.len a) (str.len (str.++ b c …)))`. The RARE matcher binds its list
variable to a list term, so it is not a template rule (`TRule`), and the step is
its own static procedure, `StaticProc.lenConcat` (`Telos/Core/Static.lean`), for
strings; `verification/TelosProofs/Core/LenConcat.lean` proves that Logos accepts
it.
-/

open Eo
open Smtm

namespace Telos.LenConcat

/-- `(str.++ b cs…)`, or `b` alone. -/
def concatOf (b : Node) (cs : List Node) : Node :=
  if cs.isEmpty then b else .app (.kind .STRING_CONCAT) ⟨b :: cs⟩

def lenNode (a : Node) : Node := .app (.kind .STRING_LENGTH) #[a]

/-- `(str.len (str.++ a b cs…))`. -/
def lhs (a b : Node) (cs : List Node) : Node := lenNode (.app (.kind .STRING_CONCAT) ⟨a :: b :: cs⟩)

/-- `(+ (str.len a) (str.len (str.++ b cs…)))`. -/
def rhs (a b : Node) (cs : List Node) : Node :=
  .app (.kind .ADD) #[lenNode a, lenNode (concatOf b cs)]

/-- The components are strings. -/
def StringsOk (a b : Node) (cs : List Node) : Prop := ∀ x ∈ a :: b :: cs, x.smtTypeF = .Seq .Char

/-- The side condition of a step from `n` to `m`. -/
def Ok (a b : Node) (cs : List Node) (n m : Node) : Prop :=
  n = lhs a b cs ∧ m = rhs a b cs ∧ StringsOk a b cs

instance (a b : Node) (cs : List Node) : Decidable (StringsOk a b cs) := by
  unfold StringsOk; infer_instance

/-- The list variable's term. -/
def tail (cs : List Node) : Term := eoRightAssocNil UserOp.str_concat (Term.String []) (cs.map Node.toEo)

/-- `[str_len_concat_rec a b (str.++ cs… "")]`. -/
def cmds (a b : Node) (cs : List Node) : CCmdList :=
  .cons (.step .str_len_concat_rec (.cons a.toEo (.cons b.toEo (.cons (tail cs) .nil))) .nil) .nil

end Telos.LenConcat
