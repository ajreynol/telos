import Telos.Rewriter.Certified

/-!
# Rule patterns

A `RuleSpec` describes how to *find* an application of one CPC rewrite rule: the
pattern of its left-hand side, which pattern variables are the rule's `:args`,
and the terms its premises evaluate. The table of all of them is generated from
the Eunoia signature (`Telos/Rules/Generated.lean`, by `scripts/gen-rules.py`).

A spec does not describe the right-hand side. Logos's program for the rule
computes it, and Logos's checker validates the step (`Telos/Rewriter/Certified.lean`).
So the specs, the generator and the matcher (`Telos/Rules/Match.lean`) are
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
  /-- The rule's left-hand side. -/
  lhs : Pat
  /-- The premises, in order. Each is discharged by an `evaluate` step (and a
  `symm` step), and the rule applies when the values match. -/
  premises : List Premise
  deriving Repr

end Telos
