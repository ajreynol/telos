import Telos

/-!
# Tests of the front end and of proof output

Each query is read by Logos's parser, rewritten, and its CPC proof printed. The
proof must be accepted by Logos twice: by its checker, before printing
(`Proof.proofOf`), and as text, re-parsed as a refutation (`logos_check_proof`),
which checks the printer. Proofs under binders use `eo::var`, which Logos's
parser does not read yet; `scripts/check-proofs.py` checks those with Ethos.
-/

open Telos Telos.Frontend

namespace TelosTests.Frontend

def script : String := "
(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const x Int)
(declare-fun f (Int) Bool)
(declare-sort U 0)
(declare-const u U)
(simplify (not (not a)))
(simplify (and a true b))
(simplify (ite (not a) b false))
(simplify (= (= x 0) true))
(simplify (or (f x) (not (not (f x)))))
(simplify (forall ((y Int)) (and (= y x) true)))
(simplify (= u u))
(simplify a)
(simplify (+ x 1))
"

/-- The output of each query, and whether its proof was printed. -/
def results : Option (List (Except String String × Bool)) := do
  let sc ← (readScript script).toOption
  return sc.queries.map fun q =>
    let r := simplify sc q true
    (r.output, match r.proof with | some (.ok _) => true | _ => false)

#guard (results.map fun rs => rs.map (·.1.toOption)) == some [
  some "a",
  some "(and a b)",
  some "(and (not a) b)",
  some "(= x 0)",
  some "(f x)",
  some "(forall ((y Int)) (= y x))",
  some "(= u u)",  -- not yet `true`: builtin equality rewriting is not ported
  some "a",
  none]

-- Every supported query has a proof that Logos accepts.
#guard (results.map fun rs => rs.map (·.2)) == some [true, true, true, true, true, true, true, true, false]

/-- A proof, as printed. -/
def proofText : Option String := do
  let sc ← (readScript script).toOption
  let q ← sc.queries[2]?
  (← (simplify sc q true).proof).toOption

#guard proofText == some "(declare-const a Bool)
(declare-const b Bool)
(declare-const x Int)
(declare-const f (-> Int Bool))
(declare-sort U 0)
(declare-const u U)
(assume @goal (not (= (ite (not a) b false) (and (not a) b))))
(step @p0 (= (ite (not a) b false) (ite a false b)) :rule ite-not-cond :args (a b false))
(step @p1 (= (ite a false b) (and (not a) b)) :rule ite-then-false :args (a b))
(step @p2 (= (ite (not a) b false) (and (not a) b)) :rule trans :premises (@p0 @p1))
(step @false false :rule contra :premises (@p2 @goal))
"

end TelosTests.Frontend
