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
  deriving Repr, Inhabited

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
  /-- For each premise `(= A v)`, the pattern of `A`. Each is discharged by an
  `evaluate` step, which proves `(= A v')`; the rule applies when `v'` is `v`. -/
  premises : List Pat
  deriving Repr

end Telos
