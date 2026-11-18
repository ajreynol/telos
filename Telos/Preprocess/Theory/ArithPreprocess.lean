import Telos.Preprocess.SkolemSteps

/-!
# Arithmetic theory preprocessing

cvc5's `TheoryArith::ppRewrite`, which is `OperatorElim::eliminate` with
`partialOnly = false` (`src/theory/arith/operator_elim.cpp`): the extended
operators are eliminated, the partial ones (`div`, `mod`, `/`) into an `ite` on
a zero divisor with the division-by-zero skolem applied to the numerator, and
the total ones (`div_total`, `mod_total`, `/_total`, `to_int`, `is_int`) into
purification skolems with a lemma bounding them. `abs` becomes an `ite`.

CPC's `arith_reduction` concludes `(and (= n m) L)` for an operator with a lemma
`L`, and `(= n m)` otherwise, with the same `m` and `L` as `OperatorElim`
(it is how cvc5 proves this step). So the result and the lemma are read from the
conclusion, with `and_elim`. Not ported: the transcendental and real algebraic
number cases (outside safe mode), and the non-linear logic check.
-/

namespace Telos.Preprocess

open Eo Node

/-- The operators `OperatorElim::eliminateOperators` eliminates, as telos has
them. `/_total` by a constant is left to the rewriter. -/
def arithEliminates (n : Node) : Bool :=
  match n.getKind with
  | .TO_INTEGER | .IS_INTEGER | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL
  | .INTS_DIVISION | .INTS_MODULUS | .DIVISION | .ABS => true
  | .DIVISION_TOTAL => !(n.getChildren[1]?.map Node.isConst).getD true
  | _ => false

/-- The eliminations that come with a skolem lemma. -/
def arithHasLemma (n : Node) : Bool :=
  match n.getKind with
  | .TO_INTEGER | .IS_INTEGER | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL
  | .DIVISION_TOTAL => true
  | _ => false

/-- `TheoryArith::ppRewrite`: the elimination of `n`, and its skolem lemma. -/
def arithPpRewrite (n : Node) : Option (Rw n × Option (Rw mkTrue)) := do
  if !arithEliminates n then none
  let red := stepWith .arith_reduction [n.toEo]
  if arithHasLemma n then
    let r ← applyCmds (cmdList [red, andElim 0]) n
    return (r, lemmaBy [red, andElim 1])
  else
    return (← applyCmds (cmdList [red]) n, none)

end Telos.Preprocess
