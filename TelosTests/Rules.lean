import Telos

/-!
# Tests of the rule database

Each generated rule is applied to its own left-hand side, instantiated with fresh
variables of one type (Boolean, Int or Real) (and `:list` variables with zero and with two elements). The
certified step must succeed: this catches generator and matcher mistakes, which
would otherwise only show up as missed rewrites. Rules that cannot fire on fresh
variables are listed in `expectedToFail`, and tested on concrete instances below.
-/

open Telos Telos.Node Eo

namespace TelosTests

/-- The n-ary operator under which the list variable `i` occurs. -/
partial def listKind? : Pat → Nat → Option Kind
  | .app k ps, i =>
    if ps.any (fun | .listVar j => i == j | _ => false) then some k
    else ps.findSome? (listKind? · i)
  | _, _ => none

def freshSubst (r : RuleSpec) (T : TypeNode) (listLen : Nat) : Subst :=
  (Array.range r.numVars).map fun i =>
    some <| match listKind? r.lhs i with
      | some k => .list k ((List.range listLen).map fun j => .var s!"l{i}_{j}" T)
      | none => .node (.var s!"v{i}" T)

/-- Whether the rule fires on its fresh left-hand side, with variables of some
type (all of the same type). -/
def firesOnFresh (r : RuleSpec) (listLen : Nat) : Bool :=
  [TypeNode.boolean, .integer, .real].any fun T =>
    match r.lhs.instantiate (freshSubst r T listLen) with
    | some n => (r.apply n).isSome
    | none => false

/-- Rules that do not fire on fresh variables of one type: their premises do not
hold there, or their variables have different types, or their right-hand sides
use kinds that `Node.ofEo` cannot read back yet. -/
def expectedToFail : List String :=
  ["arith-eq-elim-real", "arith-eq-elim-int",
   "bool-not-true", "bool-not-false", "ite-neg-branch", "eq-cond-deq",
   -- premises that need constants (tested on concrete instances in
   -- test/examples/arith.smt2)
   "arith-int-div-total", "arith-int-mod-total", "arith-int-eq-conflict",
   "arith-int-div-total-neg", "arith-int-mod-total-neg", "arith-mod-over-mod-1",
   "arith-mod-over-mod", "arith-mod-over-mod-mult",
   -- a Boolean condition with arithmetic branches: variables of two types
   "arith-geq-ite-lift", "arith-leq-ite-lift"]

def selfTestFailures (listLen : Nat) : List String :=
  generatedRules.filterMap fun r =>
    if expectedToFail.contains r.name || firesOnFresh r listLen then none else some r.name

#guard selfTestFailures 0 == []
#guard selfTestFailures 2 == []
-- Every rule listed as an exception exists.
#guard expectedToFail.all fun n => (findRule? n).isSome

/-- The result of rewriting `n` by a rule. -/
def rw? (name : String) (n : Node) : Option Node :=
  (rewriteBy name n).map (·.1)

def c : Node := .var "c" .boolean
def t : Node := .var "t" .integer
def int (i : Int) : Node := .const (.integer i)

-- Premises discharged by evaluation.
#guard rw? "bool-not-true" (notNode mkFalse) == some mkTrue
#guard rw? "bool-not-true" (notNode c) == none
#guard rw? "bool-not-false" (notNode mkTrue) == some mkFalse
#guard rw? "ite-neg-branch" (iteNode c mkFalse mkTrue) == some (eqNode c mkFalse)
#guard rw? "eq-cond-deq" (eqNode (eqNode t (int 1)) (eqNode t (int 2))) ==
  some (mkNode .AND #[notNode (eqNode t (int 1)), notNode (eqNode t (int 2))])
#guard rw? "eq-cond-deq" (eqNode (eqNode t (int 1)) (eqNode t (int 1))) == none

-- `:list` variables, and non-linear patterns.
#guard rw? "bool-or-taut" (mkNode .OR #[c, mkFalse, notNode c]) == some mkTrue
#guard rw? "bool-and-conf" (mkNode .AND #[mkTrue, notNode c, c]) == none
#guard rw? "bool-and-conf2" (mkNode .AND #[mkTrue, notNode c, c]) == some mkFalse

-- Wrong instances are rejected.
#guard rw? "ite-true-cond" (iteNode mkFalse t (int 0)) == none
#guard rw? "eq-refl" (eqNode t (int 0)) == none

-- Rewriting under a binder keeps bound variables bound.
def b : Node := .boundVar "b" .boolean
#guard rw? "bool-double-not-elim" (notNode (notNode b)) == some b

end TelosTests
