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
  [TypeNode.boolean, .integer, .real, .bitVector 4].any fun T =>
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
   "arith-geq-ite-lift", "arith-leq-ite-lift",
   -- a premise that needs a non-integral constant (tested below)
   "arith-int-geq-tighten",
   -- `bvite`: a `(_ BitVec 1)` condition with branches of another width
   "bv-ite-equal-children", "bv-ite-equal-cond-1", "bv-ite-equal-cond-2", "bv-ite-equal-cond-3",
   "bv-ite-merge-then-if", "bv-ite-merge-else-if", "bv-ite-merge-then-else", "bv-ite-merge-else-else",
   -- `concat` of operands of different widths, or premises on widths
   "bv-and-concat-pullup", "bv-or-concat-pullup", "bv-xor-concat-pullup",
   "bv-and-concat-pullup2", "bv-or-concat-pullup2", "bv-xor-concat-pullup2",
   "bv-and-concat-pullup3", "bv-or-concat-pullup3", "bv-xor-concat-pullup3",
   "bv-ult-add-one",
   -- integers and bit-vectors
   "uf-bv2nat-geq-elim",
   -- arrays, with indices and elements of other types (tested below)
   "array-read-over-write", "array-read-over-write2", "array-store-overwrite",
   "array-store-self", "array-read-over-write-split", "array-store-swap"]

/-- Whether a pattern has integer parameters (indices, widths, bit-vector
literals), which fresh variables cannot instantiate. Such rules are tested on
concrete terms (`test/examples/bv.smt2`) and by fuzzing. -/
partial def patHasIntParams : Pat → Bool
  | .indexed .. | .bvLit .. => true
  | .app _ ps => ps.any patHasIntParams
  | _ => false

def selfTestFailures (listLen : Nat) : List String :=
  generatedRules.filterMap fun r =>
    if expectedToFail.contains r.name || patHasIntParams r.lhs || firesOnFresh r listLen then none
    else some r.name

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

-- Arrays.
def arr : Node := .var "A" (.array .integer .integer)
def sel (a i : Node) : Node := mkNode .SELECT #[a, i]
def sto (a i e : Node) : Node := mkNode .STORE #[a, i, e]
#guard rw? "array-read-over-write" (sel (sto arr t (int 1)) t) == some (int 1)
#guard rw? "array-read-over-write2" (sel (sto arr (int 0) (int 1)) (int 2)) == some (sel arr (int 2))
#guard rw? "array-read-over-write2" (sel (sto arr t (int 1)) (int 2)) == none
#guard rw? "array-store-overwrite" (sto (sto arr t (int 1)) t (int 2)) == some (sto arr t (int 2))
#guard rw? "array-store-self" (sto arr t (sel arr t)) == some arr
#guard rw? "array-store-swap" (sto (sto arr (int 1) t) (int 0) t) == some (sto (sto arr (int 0) t) (int 1) t)

-- Premises discharged by evaluation; `(= cc (+ (to_int c) 1))` defines `cc`.
#guard rw? "arith-int-geq-tighten" (mkNode .GEQ #[mkNode .TO_REAL #[t], .const (.rational (mkRat 1 2))]) ==
  some (mkNode .GEQ #[t, int 1])
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
