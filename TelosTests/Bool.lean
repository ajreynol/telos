import Telos

/-!
# Tests of the Boolean rewriter

Expected results follow cvc5's `TheoryBoolRewriter` code path for each input
(`src/theory/booleans/theory_bool_rewriter.cpp`), with telos's term order in
place of node ids. Differential fuzzing against cvc5 itself comes later.
-/

open Telos Telos.Node

namespace TelosTests.Bool

def a : Node := .var "a" .boolean
def b : Node := .var "b" .boolean
def c : Node := .var "c" .boolean
def x : Node := .var "x" .integer
def y : Node := .var "y" .integer
def q : Node := .boundVar "q" .boolean

def rw (n : Node) : String := (rewrite n).toSmtLib

-- NOT
#guard rw (notNode (notNode (notNode a))) == "(not a)"
#guard rw (notNode mkTrue) == "false"
-- OR / AND: flattenNode, as cvc5 orders the children
#guard rw (mkNode .AND #[a, mkTrue, mkNode .AND #[b, a], c]) == "(and a c b)"
#guard rw (mkNode .OR #[a, mkFalse, mkNode .OR #[b, mkTrue]]) == "true"
#guard rw (mkNode .AND #[a, a, a]) == "a"
#guard rw (mkNode .OR #[mkFalse, mkFalse]) == "false"
#guard rw (mkNode .AND #[a, notNode (mkNode .OR #[mkFalse, mkNode .AND #[a, mkFalse]])]) == "a"
-- IMPLIES
#guard rw (mkNode .IMPLIES #[a, mkFalse]) == "(not a)"
#guard rw (mkNode .IMPLIES #[notNode (notNode a), mkFalse]) == "(not a)"
#guard rw (mkNode .IMPLIES #[mkTrue, a]) == "a"
-- EQUAL
#guard rw (eqNode mkTrue (mkNode .AND #[a, mkTrue])) == "a"
#guard rw (eqNode mkFalse a) == "(not a)"
#guard rw (eqNode b a) == "(= a b)"
#guard rw (eqNode (notNode a) a) == "false"
#guard rw (eqNode (eqNode x (.const (.integer 1))) (eqNode x (.const (.integer 2)))) ==
  "(and (not (= x 1)) (not (= x 2)))"
-- rewriteViaEqConstEq, in every orientation; the arithmetic rewriter orients the
-- equalities, as cvc5 does
#guard rw (eqNode (eqNode (.const (.integer 1)) x) (eqNode x (.const (.integer 2)))) ==
  "(and (not (= x 1)) (not (= x 2)))"
#guard rw (eqNode (eqNode x (.const (.integer 1))) (eqNode (.const (.integer 2)) x)) ==
  "(and (not (= x 1)) (not (= x 2)))"
#guard rw (eqNode (eqNode (.const (.integer 1)) x) (eqNode (.const (.integer 2)) x)) ==
  "(and (not (= x 1)) (not (= x 2)))"
#guard rw (eqNode (eqNode x (.const (.integer 1))) (eqNode (.const (.integer 1)) x)) == "true"
-- XOR
#guard rw (mkNode .XOR #[mkTrue, notNode a]) == "a"
#guard rw (mkNode .XOR #[a, notNode a]) == "true"
-- ITE
#guard rw (iteNode (notNode a) b c) == "(ite a c b)"
#guard rw (iteNode a mkTrue mkFalse) == "a"
#guard rw (iteNode a mkFalse mkTrue) == "(not a)"
#guard rw (iteNode a a b) == "(or a b)"
#guard rw (iteNode a b (notNode b)) == "(= a b)"
#guard rw (iteNode a (notNode b) b) == "(= a (not b))"
#guard rw (iteNode a mkTrue (notNode a)) == "true"
#guard rw (iteNode a (iteNode a b c) c) == "(ite a b c)"
#guard rw (iteNode a x (iteNode (notNode a) y x)) == "(ite a x y)"
#guard rw (iteNode mkTrue x y) == "x"
-- The then-branch is an ITE on another condition: the else-branch is still checked.
#guard rw (iteNode b (iteNode (notNode (eqNode x (.const (.integer 1)))) mkTrue
    (eqNode x (.const (.integer 1)))) (iteNode b c (mkNode .AND #[b, mkTrue, b]))) == "b"
-- Under a binder
#guard rw (forallNode #[q] (notNode (notNode q))) == "(forall ((q Bool)) q)"

end TelosTests.Bool
