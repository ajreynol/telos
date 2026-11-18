import Telos

/-!
# Tests of skolems

Skolems (`Node.skolem`) are atomic, as cvc5's `SKOLEM` variables are: the
rewriter does not enter a skolem's cache values. A function skolem is applied
with `APPLY_UF`, and its arguments are rewritten.
-/

open Telos Telos.Node

namespace TelosTests.Skolem

def x : Node := .var "x" .integer
def r : Node := .var "r" .real
def x0 : Node := mkNode .ADD #[x, .const (.integer 0)]

def k : Node := mkPurifySkolem x0
def divZ (t : Node) : Node := applyUF (.skolem .INT_DIV_BY_ZERO #[]) #[t]
def qdivZ (t : Node) : Node := applyUF (.skolem .DIV_BY_ZERO #[]) #[t]

def rw (n : Node) : String := (rewrite n).toSmtLib

-- The CPC terms, and back.
#guard Node.ofEo [] k.toEo == some k
#guard Node.ofEo [] (divZ x).toEo == some (divZ x)
#guard Node.ofEo [] (qdivZ r).toEo == some (qdivZ r)
#guard Node.ofEo [] (Node.skolem .MOD_BY_ZERO #[]).toEo == some (.skolem .MOD_BY_ZERO #[])
-- Types: Logos's, and the fast ones agree.
#guard k.getType == some .integer && k.typeHint == some .integer
#guard (divZ x).getType == some .integer
#guard (qdivZ r).getType == some .real
#guard decide (divZ x).WellTyped && !decide (divZ r).WellTyped
#guard (Node.skolem .PURIFY #[]).getType == none
#guard theoryOf k == .THEORY_ARITH
-- A skolem is atomic: its cache value is not rewritten.
#guard rw k == "(@purify (+ x 0))"
#guard rw (mkNode .ADD #[k, .const (.integer 0)]) == "(@purify (+ x 0))"
#guard rewrite (eqNode k k) == mkTrue
-- The arguments of a function skolem are.
#guard rw (divZ x0) == "(@int_div_by_zero x)"
-- Skolems are equal when their identifiers and cache values are.
#guard mkPurifySkolem x0 == k && mkPurifySkolem x != k
#guard k.vars == [k, x]

/-! ## The `theory-preprocess` pass -/

def a : Node := .var "a" .boolean
def y : Node := .var "y" .integer
def three : Node := .const (.integer 3)
def pp (as : List Node) : List String := (Preprocess.preprocess as).toList.map (·.toSmtLib)

-- A non-Boolean `ite` is purified, with its lemma after the `true` placeholder.
#guard pp [mkNode .GT #[iteNode a x y, three]] ==
  ["(>= (@purify (ite a x y)) 4)", "true",
   "(ite a (= x (@purify (ite a x y))) (= y (@purify (ite a x y))))"]
-- The same term in a second assertion gets no second lemma.
#guard pp [mkNode .GT #[iteNode a x y, three], mkNode .LT #[iteNode a x y, y]] ==
  ["(>= (@purify (ite a x y)) 4)", "(>= (+ y (* -1 (@purify (ite a x y)))) 1)", "true",
   "(ite a (= x (@purify (ite a x y))) (= y (@purify (ite a x y))))"]
-- `div` by a constant: a purification skolem, whose lemma is split.
#guard pp [mkNode .GT #[mkNode .INTS_DIVISION #[x, three], three]] ==
  ["(>= (@purify (div_total x 3)) 4)", "true",
   "(>= (+ x (* -3 (@purify (div_total x 3)))) 0)",
   "(not (>= (+ x (* -3 (@purify (div_total x 3)))) 3))"]
-- Division by zero: the skolem function, applied.
#guard pp [mkNode .GT #[mkNode .INTS_DIVISION #[x, .const (.integer 0)], three]] ==
  ["(>= (@int_div_by_zero x) 4)", "true"]

end TelosTests.Skolem
