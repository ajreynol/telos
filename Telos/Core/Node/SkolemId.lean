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
  /-- `(@quantifiers_skolemize q i)`, with cache values a quantified formula
  `q` and an integer `i`: the witness of its `i`-th variable when `q` is false
  (`Skolemize::getSkolemConstant`). Its CPC term is the binary operator
  `@quantifiers_skolemize` of `q` and the numeral `i`. -/
  | QUANTIFIERS_SKOLEMIZE
  /-- `(@re_unfold_pos_component s r i)`, with cache values a string `s`, a
  regular expression `r` (a concatenation) and an integer `i`: the `i`-th
  component of `s` in the unfolding of `(str.in_re s r)`
  (`RegExpOpr::reduceRegExpPos`). Its CPC term is the ternary operator
  `@re_unfold_pos_component`. -/
  | RE_UNFOLD_POS_COMPONENT
  /-- `@strings_stoi_result`, of type `(-> Int Int)`, with cache value a string `s`:
  `(@strings_stoi_result s i)` is the integer of its first `i` digits. -/
  | STRINGS_STOI_RESULT
  /-- `@strings_stoi_non_digit`, an integer, with cache value a string: the position of
  its first character that is not a digit. -/
  | STRINGS_STOI_NON_DIGIT
  /-- `@strings_itos_result`, of type `(-> Int Int)`, with cache value an integer `n`:
  the integer of the first digits of `(str.from_int n)`. -/
  | STRINGS_ITOS_RESULT
  /-- `@strings_num_occur`, an integer, with cache values strings `x` and `y`: the
  number of occurrences of `y` in `x`. -/
  | STRINGS_NUM_OCCUR
  /-- `@strings_num_occur_re`, an integer, as `STRINGS_NUM_OCCUR`, of a regular
  expression. -/
  | STRINGS_NUM_OCCUR_RE
  /-- `@strings_occur_index`, of type `(-> Int Int)`, with cache values strings `x`
  and `y`: the position after the `i`-th occurrence of `y` in `x`. -/
  | STRINGS_OCCUR_INDEX
  /-- `@strings_occur_index_re`, as `STRINGS_OCCUR_INDEX`, of a regular expression. -/
  | STRINGS_OCCUR_INDEX_RE
  /-- `@strings_replace_all_result`, of type `(-> Int String)`, with cache values
  strings `x`, `y` and `z`: what `str.replace_all` gives of the rest of `x` after
  the `i`-th occurrence of `y`. -/
  | STRINGS_REPLACE_ALL_RESULT
  /-- `@strings_replace_re_all_result`, as `STRINGS_REPLACE_ALL_RESULT`, of a
  regular expression. -/
  | STRINGS_REPLACE_RE_ALL_RESULT
  deriving DecidableEq, Repr, Inhabited, Hashable, Ord

namespace SkolemId

/-- All skolem identifiers (for reading CPC terms back). -/
def all : List SkolemId := [.PURIFY, .INT_DIV_BY_ZERO, .MOD_BY_ZERO, .DIV_BY_ZERO, .SETS_DEQ_DIFF,
  .QUANTIFIERS_SKOLEMIZE, .RE_UNFOLD_POS_COMPONENT, .STRINGS_STOI_RESULT,
  .STRINGS_STOI_NON_DIGIT,
  .STRINGS_ITOS_RESULT,
  .STRINGS_NUM_OCCUR,
  .STRINGS_NUM_OCCUR_RE,
  .STRINGS_OCCUR_INDEX,
  .STRINGS_OCCUR_INDEX_RE,
  .STRINGS_REPLACE_ALL_RESULT,
  .STRINGS_REPLACE_RE_ALL_RESULT]

/-- The number of cache values of a skolem with this identifier. -/
def numCacheVals : SkolemId → Nat
  | .PURIFY => 1
  | .INT_DIV_BY_ZERO | .MOD_BY_ZERO | .DIV_BY_ZERO => 0
  | .SETS_DEQ_DIFF => 2
  | .QUANTIFIERS_SKOLEMIZE => 2
  | .RE_UNFOLD_POS_COMPONENT => 3
  | .STRINGS_STOI_RESULT => 1
  | .STRINGS_STOI_NON_DIGIT => 1
  | .STRINGS_ITOS_RESULT => 1
  | .STRINGS_NUM_OCCUR => 2
  | .STRINGS_NUM_OCCUR_RE => 2
  | .STRINGS_OCCUR_INDEX => 2
  | .STRINGS_OCCUR_INDEX_RE => 2
  | .STRINGS_REPLACE_ALL_RESULT => 3
  | .STRINGS_REPLACE_RE_ALL_RESULT => 3

/-- The function skolems of the theory of strings, of one argument. -/
def isStringsFn : SkolemId → Bool
  | .STRINGS_STOI_RESULT | .STRINGS_ITOS_RESULT | .STRINGS_OCCUR_INDEX | .STRINGS_OCCUR_INDEX_RE
  | .STRINGS_REPLACE_ALL_RESULT | .STRINGS_REPLACE_RE_ALL_RESULT => true
  | _ => false

/-- The CPC name of the skolem's operator, as cvc5 prints it. -/
def name : SkolemId → String
  | .PURIFY => "@purify"
  | .INT_DIV_BY_ZERO => "@int_div_by_zero"
  | .MOD_BY_ZERO => "@mod_by_zero"
  | .DIV_BY_ZERO => "@div_by_zero"
  | .SETS_DEQ_DIFF => "@sets_deq_diff"
  | .QUANTIFIERS_SKOLEMIZE => "@quantifiers_skolemize"
  | .RE_UNFOLD_POS_COMPONENT => "@re_unfold_pos_component"
  | .STRINGS_STOI_RESULT => "@strings_stoi_result"
  | .STRINGS_STOI_NON_DIGIT => "@strings_stoi_non_digit"
  | .STRINGS_ITOS_RESULT => "@strings_itos_result"
  | .STRINGS_NUM_OCCUR => "@strings_num_occur"
  | .STRINGS_NUM_OCCUR_RE => "@strings_num_occur_re"
  | .STRINGS_OCCUR_INDEX => "@strings_occur_index"
  | .STRINGS_OCCUR_INDEX_RE => "@strings_occur_index_re"
  | .STRINGS_REPLACE_ALL_RESULT => "@strings_replace_all_result"
  | .STRINGS_REPLACE_RE_ALL_RESULT => "@strings_replace_re_all_result"

end SkolemId

end Telos
