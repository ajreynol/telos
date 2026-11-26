import Telos.Core.Certified

/-!
# Rule patterns

A `RuleSpec` describes how to *find* an application of one CPC rewrite rule: the
pattern of its left-hand side, which pattern variables are the rule's `:args`,
and the terms its premises evaluate. The table of all of them is generated from
the Eunoia signature (`Telos/Rewriter/Rules/Generated.lean`, by `scripts/gen-rules.py`).

Logos's checker validates each step (`Telos/Core/Certified.lean`). A spec may
also describe the right-hand side, so that the result need not be read back from
the term Logos's program computes; where it does not, or where that is another
term, the result is read back. So the specs, the generator and the matcher (`Telos/Rewriter/Rules/Match.lean`) are
untrusted: a wrong spec only means that a rewrite is missed.
-/

open Eo

namespace Telos

/-- The pattern of a rule's left-hand side, in telos kinds. -/
inductive Pat where
  /-- Pattern variable `i`, matching one node. A variable that occurs twice must
  match equal nodes. -/
  | var (i : Nat)
  /-- Pattern variable `i` of a `:list` parameter, matching a (possibly empty)
  run of children of the enclosing n-ary application. -/
  | listVar (i : Nat)
  | const (c : Const)
  | app (k : Kind) (args : List Pat)
  /-- An application of an indexed operator, like `(extract i j x)`. Each index
  pattern matches the index as an integer constant. -/
  | indexed (k : Kind) (indices : List Pat) (args : List Pat)
  /-- A bit-vector literal `(@bv value width)`: the patterns match the value and
  the width as integer constants. -/
  | bvLit (value width : Pat)
  /-- In a right-hand side, `(eo::list_singleton_elim f (f …))`: the application of
  the n-ary kind `k`, or its only element. -/
  | elim (k : Kind) (args : List Pat)
  deriving Repr, Inhabited

/-- A premise of a rule, discharged by evaluation: `(= value expr)` when `symm`,
and `(= expr value)` otherwise. -/
structure Premise where
  /-- The term that is evaluated. -/
  expr : Pat
  /-- The pattern of its value. Variables of `value` not bound yet are bound to
  the value: this is how a rule defines arguments, as in
  `(= wm (- (@bvsize x) 1))`. -/
  value : Pat
  /-- Whether the premise is `(= value expr)`, proven by `symm` of the
  evaluation. -/
  symm : Bool := false
  /-- For a premise `(= expr other)` between two terms: both are evaluated, and
  their values must be equal (proven by `evaluate`, `evaluate`, `symm` and
  `trans`). `value` is then unused. -/
  other : Option Pat := none
  deriving Repr

/-- One CPC rewrite rule, as far as finding its applications goes. -/
structure RuleSpec where
  /-- The Eunoia name of the rule, for example `bool-double-not-elim`. -/
  name : String
  rule : CRule
  /-- The number of pattern variables. -/
  numVars : Nat
  /-- The rule's `:args`, as pattern variables, in order. -/
  args : List Nat
  /-- Type arguments: `(p, i)` inserts, at position `p` of the arguments, the
  Eunoia type of pattern variable `i` (for rules like `str-substr-empty-range`,
  whose argument `(Seq @T0)` is the type of `x1`). -/
  typeArgs : List (Nat × Nat) := []
  /-- The rule's left-hand side. -/
  lhs : Pat
  /-- The rule's right-hand side, where telos can write it. -/
  rhs : Option Pat := none
  /-- The premises, in order. Each is discharged by an `evaluate` step (and a
  `symm` step), and the rule applies when the values match. -/
  premises : List Premise
  /-- The type the signature declares for each pattern variable, when it is a
  fixed type telos has (for tests; matching does not use it). -/
  varTypes : List (Option TypeNode) := []
  deriving Repr

end Telos
