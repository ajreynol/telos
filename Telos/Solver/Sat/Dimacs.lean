import Telos.Solver.Sat.Minisat

/-!
# Propositional solving, for testing the SAT solver

MiniSat with no theories: the theory proxy does nothing. `telos --dimacs FILE`
solves a DIMACS CNF file and prints `sat` (with a model, checked against the
clauses) or `unsat`. For testing the SAT layer alone
(`scripts/fuzz-sat.py`).
-/

namespace Telos.Sat

/-- No theories. -/
instance : TheoryProxy (StateM Solver) where
  theoryCheck _ := pure ()
  theoryPropagate := pure #[]
  explainPropagation l := pure #[l]
  enqueueTheoryLiteral _ := pure ()
  contextPush := pure ()
  contextPop := pure ()
  notifyBacktrack := pure ()
  getNextDecisionRequest := pure (Lit.undef, false, false)
  isDecisionEngineDone := pure false
  theoryNeedCheck := pure false
  notifySatClause _ := pure ()
  notifyRestart := pure ()

/-- The clauses of a DIMACS file, as lists of nonzero integers. -/
def parseDimacs (text : String) : Except String (Nat × Array (Array Int)) := do
  let mut clauses : Array (Array Int) := #[]
  let mut cur : Array Int := #[]
  let mut nvars := 0
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then continue
    if line.startsWith "p" then
      match (line.splitOn " ").filter (· != "") with
      | [_, _, v, _] => nvars := v.toNat!
      | _ => throw s!"bad header: {line}"
      continue
    for tok in (line.splitOn " ").filter (· != "") do
      let some n := tok.toInt? | throw s!"bad literal: {tok}"
      if n == 0 then
        clauses := clauses.push cur
        cur := #[]
      else cur := cur.push n
  return (nvars, clauses)

/-- The literal of a DIMACS integer, over variables after `true` and `false`. -/
def ofDimacs (n : Int) : Lit := Lit.mk (n.natAbs + 1) (n < 0)

/-- Solve a DIMACS problem: the answer, and the model (DIMACS integers) for
`sat`, checked to satisfy the clauses. -/
def solveDimacs (text : String) : Except String String := do
  let (nvars, clauses) ← parseDimacs text
  let act : StateM Solver Solver.Result := do
    Solver.init
    for _ in [0:nvars] do let _ ← Solver.newVar
    for c in clauses do
      if !(← Solver.addClause (c.map ofDimacs) false) then return .unsat
    Solver.solve
  let (r, s) := act.run {}
  match r with
  | .sat =>
    let val (n : Int) : Bool := s.model[n.natAbs + 1]! == LBool.ofBool (n > 0)
    if !clauses.all (·.any val) then throw "the model does not satisfy the clauses"
    let lits := (List.range nvars).map fun (i : Nat) =>
      let v : Int := (i : Int) + 1
      if s.model[i + 2]! == LBool.tt then v else -v
    return "sat\nv " ++ " ".intercalate (lits.map toString) ++ " 0"
  | .unsat => return "unsat"
  | .unknown => return "unknown"

end Telos.Sat
