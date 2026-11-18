import Telos.Frontend.Script
import Telos.Rewriter.Rewrite
import Telos.Core.Proof.Emit

/-!
# `simplify` queries

Rewrites the term of each `(simplify t)` of a script (`Telos/Frontend/Script.lean`),
as cvc5 does, optionally with its CPC proof.
-/

open Eo
open Logos
open SmtEval

namespace Telos.Frontend

/-- The result of simplifying one term. -/
structure Result where
  source : String
  /-- The rewritten term, in SMT-LIB syntax, or an error. -/
  output : Except String String
  /-- The CPC proof of the rewrite, if requested: Eunoia commands in parentheses,
as cvc5's `get-proof` prints a proof. -/
  proof : Option (Except String String) := none

/-- Rewrite `t`; with `withProof`, also print its CPC proof, checked by Logos. -/
def simplify (sc : Script) (q : Query) (withProof : Bool) : Result :=
  match q.node with
  | .error e => { source := q.source, output := .error e }
  | .ok t =>
    if !decide t.WellTyped then
      { source := q.source, output := .error "the term is not well typed" }
    else
      let r := rewriteCert t
      let proof := if withProof then
        some (do
          let p ← Proof.proofOf r
          let text := p.render sc.names sc.decls t r.1
          -- Check that Logos reads the printed proof back and accepts it.
          match logos_check_proof text with
          -- In parentheses, as cvc5's `get-proof` prints a proof.
          | .ok .correct => pure ("(\n" ++ text ++ ")\n")
          | .ok _ => throw "internal error: Logos does not accept the printed proof"
          | .error e => throw s!"internal error: Logos cannot parse the printed proof: {e}")
        else none
      { source := q.source, output := .ok (r.1.toSmtLibWith sc.dtNames), proof }

end Telos.Frontend
