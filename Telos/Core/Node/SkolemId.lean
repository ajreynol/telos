/-!
# Skolem identifiers

cvc5's `SkolemId` (`src/expr/skolem_manager.h`, `include/cvc5/cvc5_skolem_id.h`):
what a skolem stands for. A skolem is `Node.skolem id cacheVals`, cvc5's
`SkolemManager::mkSkolemFunction(id, cacheVals)`. Only the identifiers that the
ported passes introduce are listed; each has a CPC term (`SkolemId.eoShape`)
whose value Logos defines.
-/

namespace Telos

inductive SkolemId where
  /-- `(@purify t)`, with cache value `t`: the purification skolem of `t`, whose
  value is that of `t`. -/
  | PURIFY
  /-- `@int_div_by_zero`, of type `(-> Int Int)`, no cache values: the value of
  `(div x 0)` is `(@int_div_by_zero x)`. -/
  | INT_DIV_BY_ZERO
  /-- `@mod_by_zero`, of type `(-> Int Int)`: the value of `(mod x 0)`. -/
  | MOD_BY_ZERO
  /-- `@div_by_zero`, of type `(-> Real Real)`: the value of `(/ x 0.0)`. -/
  | DIV_BY_ZERO
  /-- `(@sets_deq_diff A B)`, with cache values `A` and `B`, two sets: an element
  in exactly one of them when they differ (the theory of sets' `SETS_DEQ`). -/
  | SETS_DEQ_DIFF
  deriving DecidableEq, Repr, Inhabited, Hashable, Ord

namespace SkolemId

/-- All skolem identifiers (for reading CPC terms back). -/
def all : List SkolemId := [.PURIFY, .INT_DIV_BY_ZERO, .MOD_BY_ZERO, .DIV_BY_ZERO, .SETS_DEQ_DIFF]

/-- The number of cache values of a skolem with this identifier. -/
def numCacheVals : SkolemId → Nat
  | .PURIFY => 1
  | .INT_DIV_BY_ZERO | .MOD_BY_ZERO | .DIV_BY_ZERO => 0
  | .SETS_DEQ_DIFF => 2

/-- The CPC name of the skolem's operator, as cvc5 prints it. -/
def name : SkolemId → String
  | .PURIFY => "@purify"
  | .INT_DIV_BY_ZERO => "@int_div_by_zero"
  | .MOD_BY_ZERO => "@mod_by_zero"
  | .DIV_BY_ZERO => "@div_by_zero"
  | .SETS_DEQ_DIFF => "@sets_deq_diff"

end SkolemId

end Telos
