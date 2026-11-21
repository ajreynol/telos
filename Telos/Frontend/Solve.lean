import Telos.Frontend.PostAsserts
import Telos.Solver.Engine
import Telos.Solver.Prop
import Telos.Solver.EqProofCpc

/-!
# `--theory-events`: solving conjunctions of literals

Preprocesses a benchmark as `--post-asserts` does, then gives the result to
the theory engine (`Telos/Solver/Engine.lean`) if it is a conjunction of
literals, and prints the engine's events as cvc5 prints them with
`-o theory-events` (`cvc5-theory-events.patch`), then the answer.

The literals are those of the preprocessed assertions, split at a top-level
`and`, as cvc5's CNF stream asserts the children of a top-level `and` as units.
The engine works on the skolems themselves; they are printed as
`--post-asserts` names them (`@purify_1`, …).

An `unsat` answer means that the input assertions are unsatisfiable
(`verification/TelosProofs/Solver/Solve.lean`): the engine's certificate
refutes the literals, which hold in every model of the preprocessed
assertions, which are equivalent to the input ones.

Anything else (a disjunction, an `ite`, a Boolean equality) has SAT structure,
which telos does not handle yet: the input is reported as unsupported.

With `preprocess := false` (`--no-preprocess`), the assertions are given to the
engine as they are: for testing the engine on inputs that are already
preprocessed, such as cvc5's `-o post-asserts` output, whose equalities cvc5
orients by node id. The engine assumes nothing about its input for soundness
(`docs/theory-engine-plan.md`, "Preprocessed inputs").
-/

namespace Telos.Frontend

open Solver

/-- Whether `n` is a Boolean connective that cvc5's CNF stream translates into
clauses, rather than an atom. -/
def isConnective : Node → Bool
  | .app (.kind k) cs =>
    match k with
    | .NOT | .AND | .OR | .IMPLIES | .XOR | .ITE => true
    | .EQUAL => cs[0]?.bind Node.typeHint == some .boolean
    | _ => false
  | _ => false

/-- A literal: an atom, or the negation of one. -/
def isLiteral (n : Node) : Bool :=
  match n with
  | .app (.kind .NOT) #[a] => !isConnective a
  | _ => !isConnective n

/-- The literals of a preprocessed assertion: `true` has none, a conjunction of
literals its conjuncts, a literal itself; `none` otherwise. (The rewriter
flattens nested conjunctions.) -/
def conjLiterals (n : Node) : Option (List Node) :=
  if n == Node.mkTrue then some []
  else match n with
    | .app (.kind .AND) cs =>
      if 2 ≤ cs.size && cs.all isLiteral then some cs.toList else none
    | _ => if isLiteral n then some [n] else none

/-- The assertions given to the engine: the input assertions `as`, preprocessed
with the options `opts` unless `preprocess` is false. The preprocessed ones are
the conjuncts of the pipeline but its last, the definitions slot
(`Pipeline.assertions`). -/
def engineAssertions (as : List Node) (opts : Preprocess.PPOptions) (preprocess : Bool)
    (o : NodeOrder := {}) : List Node :=
  if as.isEmpty || !preprocess then as else
    match (Preprocess.preprocessCert as opts o).1 with
    | .app (.kind .AND) cs => if 2 ≤ cs.size then cs.toList.dropLast else [.app (.kind .AND) cs]
    | n => [n]

/-- The definitions of the variables that preprocessing solved (`x := t`), from
the pipeline's definitions slot. -/
def engineDefs (as : List Node) (opts : Preprocess.PPOptions) (preprocess : Bool)
    (o : NodeOrder := {}) : List (Node × Node) :=
  if as.isEmpty || !preprocess then [] else
    let p := Preprocess.preprocessCert as opts o
    (Preprocess.Pipeline.defs p).filterMap fun
      | .app (.kind .EQUAL) #[x@(.var ..), t] => some (x, t)
      | _ => none

/-- The literals of the assertions, or the first that is not a conjunction of
literals. -/
def literalsOf (out : List Node) : Except Node (List Node) :=
  out.foldlM (fun acc a => match conjLiterals a with
    | some ls => .ok (acc ++ ls)
    | none => .error a) []

/-- A `distinct` atom, which the UF solver does not handle (cvc5's
`DistinctExtension`). -/
def isDistinct (l : Node) : Bool :=
  match (atomOf l).1 with
  | .app (.kind .DISTINCT) _ => true
  | _ => false

/-- The literals of the assertions `out` given to the engine, or why they are
not supported; `named` prints a node with its skolems named. -/
def engineLiterals (named : Node → String) (out : List Node) : Except String (List Node) :=
  match literalsOf out with
  | .ok ls =>
    match ls.find? isDistinct with
    | some l => .error s!"unsupported: the literal {named l} is a distinct"
    | none => .ok ls
  | .error a => .error s!"unsupported: the preprocessed assertion {named a} is not a conjunction of literals"

theorem engineLiterals_ok {named : Node → String} {out lits : List Node}
    (h : engineLiterals named out = .ok lits) : literalsOf out = .ok lits := by
  unfold engineLiterals at h
  split at h
  · rename_i ls hl
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h; exact hl
  · simp at h

/-- Some atom of the formulas is a `distinct`, which the UF solver does not
handle. -/
def hasDistinctAtom (out : List Node) : Bool :=
  out.any fun f => (formulaAtoms f #[]).any isDistinct

/-- The assertions go to the SAT solver (`Solver.runSat`): they are not a
conjunction of literals, or `viaSat` asks for it, or arithmetic is enabled
(whose unate lemmas need the SAT solver), and the engine handles the theories. -/
def useSat (cfg : Solver.Config) (out : List Node) (viaSat : Bool) : Bool :=
  cfg.satSupported && !hasDistinctAtom out &&
    (viaSat || cfg.arithSolver || (literalsOf out matches .error _))

/-- cvc5's node ids, approximated, for the rewriter (`inputOrder`) when
imitating cvc5's order; else the structural order. -/
def orderFor (cvc5Order : Bool) (sc : Script) (as : List Node) : NodeOrder :=
  if cvc5Order then inputOrder sc as else {}

/-- Solve the assertions of `sc`: the assertions given to the engine, and the
engine's result. A conjunction of literals goes to the engine alone
(`Solver.run`), and to the SAT solver too if a theory sends a lemma; anything
else to the SAT solver and the engine (`Solver.runSat`), as do conjunctions
with `viaSat`. -/
def solveScript (sc : Script) (u : Preprocess.UserOptions := {}) (eeEvents : Bool := false)
    (preprocess : Bool := true) (wantProof : Bool := false) (cvc5Order : Bool := true)
    (viaSat : Bool := false) :
    Except String (List Node × Solver.Result) := do
  let theories ← enabledTheories (sc.logic.getD "ALL")
  let (opts, as) ← ppInput sc u
  let order := orderFor cvc5Order sc as
  let out := engineAssertions as opts preprocess order
  let named (n : Node) : String :=
    (substSkolems ((namedSkolems sc.dtNames out).map fun (k, v, _) => (k, v)) n).toSmtLibLet sc.dtNames
  let cfg : Solver.Config := { theories, termBased := opts.termBased, eeEvents, wantProof, cvc5Order,
                                arith := { Solver.arithOptionsOf (sc.logic.getD "ALL") with order },
                                order,
                                decision := Solver.decisionModeOf (sc.logic.getD "ALL") (u.decision <|> sc.decision),
                                declOrder := (sc.symbols.flatMap (·.names)).zipIdx.foldl
                                  (fun m (x, i) => m.insert x i) {} }
  let r ← if useSat cfg out viaSat then pure (Solver.runSat cfg out) else do
    let lits ← engineLiterals named out
    let r := Solver.run cfg lits
    -- the engine alone stops at a lemma (`unknown`, with nothing uncertified):
    -- the SAT solver is then needed
    pure (if r.answer == .unknown && r.uncertified.isNone && cfg.ufSolver then Solver.runSat cfg out else r)
  -- a `sat` stands only if its model satisfies the input assertions
  let r := if r.answer != .sat then r else
    let M := buildModel r.ee (relevantTerms r.asserted) (freeConsts as) (engineDefs as opts preprocess order) as
      r.arithModel
    if M.satisfies as then { r with model := some M }
    else { r with answer := .unknown, uncertified := some "the model does not satisfy the input" }
  return (out, r)

/-- Preprocess `sc`, solve the result if it is a conjunction of literals, and
print the events and the answer; also why an `unsat` of the engine was not
certified, if it was not (the answer is then `unknown`), and with `withProof`
the CPC refutation of the literals of a certified `unsat`
(`Telos/Solver/EqProofCpc.lean`), whose skolems are their CPC terms. Skolems
are printed as `--post-asserts` names them in the events. -/
def theoryEvents (sc : Script) (u : Preprocess.UserOptions := {}) (eeEvents : Bool := false)
    (preprocess : Bool := true) (withProof : Bool := false) (cvc5Order : Bool := true)
    (viaSat : Bool := false) :
    Except String (String × Option String × Option (Except String String)) := do
  let (out, r) ← solveScript sc u eeEvents preprocess withProof cvc5Order viaSat
  -- the skolems of the input, then those that lemmas introduced
  let σ := (namedSkolems sc.dtNames (out ++ r.events.toList.flatMap Event.nodes)).map fun (k, v, _) => (k, v)
  let lines := r.events.toList.map fun e => (e.map (substSkolems σ)).print sc.dtNames
  let proof := if !withProof then none else
    match r.cert with
    | some (A, p) => some (renderRefutation sc.names sc.decls A p)
    | none => none
  let note := match r.uncertified with
    | some e => some s!"answer not certified ({e}): answering unknown"
    | none => if r.byCertificate then some "unsat by certificate (the verified explanation did not apply)" else none
  return ("\n".intercalate (lines ++ [r.answer.name]) ++ "\n", note, proof)

end Telos.Frontend
