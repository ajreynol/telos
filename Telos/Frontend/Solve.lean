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

/-- The assertions given to the engine (`engineAssertions`), and the order of
the engine: the nodes that preprocessing created come after the input's, in
the order the pipeline's certificate creates them (`certNodes`). One run of
the preprocessor gives both. -/
def preprocessed (as : List Node) (opts : Preprocess.PPOptions) (preprocess : Bool)
    (o : NodeOrder := {}) : List Node × NodeOrder :=
  if as.isEmpty || !preprocess then (as, o) else
    let p := Preprocess.preprocessCert as opts o
    let out := match p.1 with
      | .app (.kind .AND) cs => if 2 ≤ cs.size then cs.toList.dropLast else [.app (.kind .AND) cs]
      | n => [n]
    (out, if o.decl.isEmpty && o.ids.isEmpty then o else
      Profile.time "order" (fun _ => "certNodes") fun _ => Preprocess.Pipeline.order p o)

theorem preprocessed_fst (as : List Node) (opts : Preprocess.PPOptions) (pp : Bool) (o : NodeOrder) :
    (preprocessed as opts pp o).1 = engineAssertions as opts pp o := by
  unfold preprocessed engineAssertions
  split <;> rfl

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
conjunction of literals, or `viaSat` asks for it, or arithmetic or sets are
enabled (whose lemmas need the SAT solver), and the engine handles the
theories. -/
def useSat (cfg : Solver.Config) (out : List Node) (viaSat : Bool) : Bool :=
  cfg.satSupported && !hasDistinctAtom out &&
    (viaSat || cfg.arithSolver || cfg.setsSolver || cfg.stringsSolver || (literalsOf out matches .error _))

/-- cvc5's node ids, approximated, for the rewriter (`inputOrder`) when
imitating cvc5's order; else the structural order. -/
def orderFor (cvc5Order : Bool) (sc : Script) (as : List Node) : NodeOrder :=
  if cvc5Order then Profile.time "order" (fun _ => "input") fun _ => inputOrder sc as else {}

/-- Why the model does not satisfy the assertions: the first that is not true,
and its value. -/
def modelRejection (N : DtNames) (M : Solver.Model) (as : List Node) : Solver.Unknown :=
  -- (into conjunctions: the first conjunct that is not true)
  let rec culprit (fuel : Nat) (a : Node) : Node :=
    match fuel, a with
    | fuel + 1, .app (.kind .AND) cs =>
      match cs.find? fun c => M.eval c != some (.bool true) with
      | some c => culprit fuel c
      | none => a
    | _, _ => a
  let why := match as.find? fun a => M.eval a != some (.bool true) with
    | some a =>
      let a := culprit 1000 a
      let v := match M.eval a with
        | some (.bool false) => "false"
        | some _ => "a non-Boolean value"
        | none => "not evaluated"
      let isFalse := match M.eval a with
        | some (.bool false) => true
        | _ => false
      -- the values of its constants
      let rec showV (v : Solver.MVal) : String := match v with
        | .bool b => toString b
        | .int k => toString k
        | .rat q => toString q
        | .uval s i => s!"@u{s}_{i}"
        | .fn fid .. => s!"@table{fid}"
        | .dtc s _ i =>
          let s := String.ofList (s.map Char.ofNat)
          (N.cons (DtNames.baseName s) i).getD s!"{s}.c{i}"
        | .app f a => s!"({showV f} {showV a})"
        | _ => "…"
      let vars := (a.vars.take 12).filterMap fun (x : Node) => match x with
        | .var name T => (M.const name T).map fun v => s!"{name}={showV v}"
        | _ => none
      -- (if not evaluated: its innermost subterm not evaluated, below no binder)
      let rec inner (fuel : Nat) (t : Node) : Node :=
        match fuel, t with
        | fuel + 1, .app op cs =>
          if op.getKind.isQuantifier then t else
          match cs.find? fun c => M.eval c == none with
          | some c => inner fuel c
          | none => t
        | _, _ => t
      let sub := if M.eval a == none then
          let t := inner 1000 a
          if t == a then "" else s!" [at {(t.toSmtLibLet N).take 160}]"
        else ""
      (isFalse, s!": {(a.toSmtLibLet N).take 300} is {v}{sub} (with {", ".intercalate vars})")
    | none => if M.tablesOk && M.constsOk then (true, "")
      else (false, ": its tables or constants are ill-typed")
  let d := s!"the model does not satisfy the input{why.2}"
  if why.1 then .modelFalse d else .modelNotEvaluated d

/-- A term of the formulas that the engine does not reason about: it treats
it as an uninterpreted term, so a `sat` answer rests on the model check alone,
and a model it cannot evaluate is a gap of the solver, not a failure of its
certificate. The kinds: equalities of regular expressions (the strings solver
has memberships only), and updates of tuples (the model check does not evaluate
them). -/
partial def unhandledTerm? (fs : List Node) : Option Node := Id.run do
  let mut seen : Std.HashSet Key := {}
  let mut work := fs.toArray
  while !work.isEmpty do
    let t := work.back!
    work := work.pop
    if seen.contains ⟨t⟩ then continue
    seen := seen.insert ⟨t⟩
    match t with
    | .app op cs =>
      let k := op.getKind
      if k == .TUPLE_UPDATE then return some t
      if k == .EQUAL && (cs[0]?.bind Node.typeHint) == some .regExp then return some t
      work := work ++ cs
    | _ => pure ()
  return none

/-- Why a model that does not satisfy the input was found: a part of cvc5 that
a theory does not port, on which the `sat` rested (`restsOnModel`), a term the
engine does not reason about, or else a failure of the certificate. -/
def rejectionWhy (N : DtNames) (r : Solver.Result) (M : Solver.Model) (as out : List Node) : Solver.Unknown :=
  -- a string longer than the model builder writes down (`classValues`)
  let tooLong := r.arithModel.find? fun (n, q) => n.getKind == .STRING_LENGTH && q > 1000000
  match r.restsOnModel, unhandledTerm? (as ++ out), tooLong with
  | some w, _, _ => w
  | none, some t, _ => .notPorted s!"the engine treats {(t.toSmtLibLet N).take 120} as uninterpreted (not ported)"
  | none, none, some (n, q) =>
    .modelNotEvaluated s!"{(n.toSmtLibLet N).take 80} is {q}: a string too long to write down"
  | none, none, none => modelRejection N M as

/-- A `sat` whose model was rejected, for the reason `w`: `unknown`. -/
def rejectModel (r : Solver.Result) (w : Solver.Unknown) : Solver.Result :=
  { r with answer := .unknown, why := some w }

@[simp] theorem rejectModel_answer (r : Solver.Result) (w : Solver.Unknown) : (rejectModel r w).answer = .unknown := rfl

/-- The model is accepted for the assertions: it satisfies them, or (if it does
not evaluate them: quantifiers that the rewriter removes, operators that
preprocessing eliminates) what preprocessing makes of them, which is equivalent
to them (`preprocess_correct`). -/
def accepts (M : Solver.Model) (as : List Node) (opts : Preprocess.PPOptions) (preprocess : Bool)
    (o : NodeOrder) : Bool :=
  M.satisfies as || (preprocess && M.satisfies [(Preprocess.preprocessCert as opts o).1])

/-- Solve the assertions of `sc`: the assertions given to the engine, and the
engine's result. A conjunction of literals goes to the engine alone
(`Solver.run`), and to the SAT solver too if a theory sends a lemma; anything
else to the SAT solver and the engine (`Solver.runSat`), as do conjunctions
with `viaSat`. -/
def solveScript (sc : Script) (u : Preprocess.UserOptions := {}) (eeEvents : Bool := false)
    (preprocess : Bool := true) (wantProof : Bool := false) (cvc5Order : Bool := true)
    (viaSat : Bool := false) (triggerEvents : Bool := false) (events : Bool := true) :
    Except String (List Node × Solver.Result) := do
  let theories ← enabledTheories (sc.logic.getD "ALL")
  let (opts, as) ← ppInput sc u
  let order := orderFor cvc5Order sc as
  let pre := preprocessed as opts preprocess order
  let out := pre.1
  -- the order of the engine, with the nodes that preprocessing created
  let engOrder := pre.2
  let named (n : Node) : String :=
    (substSkolems ((namedSkolems sc.dtNames out).map fun (k, v, _) => (k, v)) n).toSmtLibLet sc.dtNames
  let cfg : Solver.Config := { theories, inert := Solver.inertTheories theories (out ++ as), termBased := opts.termBased, eeEvents, triggerEvents, events, wantProof, cvc5Order,
                                traceEvents := u.traceEvents,
                                arith := { Solver.arithOptionsOf (sc.logic.getD "ALL") with order := engOrder },
                                order := engOrder,
                                pureArith := Solver.pureArithOf (sc.logic.getD "ALL"),
                                decision := Solver.decisionModeOf (sc.logic.getD "ALL") (u.decision <|> sc.decision),
                                declOrder := (sc.symbols.flatMap (·.names)).zipIdx.foldl
                                  (fun m (x, i) => m.insert x i) {} }
  let r ← if useSat cfg out viaSat then pure (Solver.runSat cfg out) else do
    let lits ← engineLiterals named out
    let r := Solver.run cfg lits
    -- the engine alone stops at a lemma (`unknown`, with nothing uncertified):
    -- the SAT solver is then needed
    pure (if r.answer == .unknown && !(r.why.any Solver.Unknown.isCertFailure) && cfg.satSupported then
      Solver.runSat cfg out else r)
  -- a `sat` stands only if its model satisfies the input assertions
  let r := if r.answer != .sat then r else
    let M := buildModel r.ee (relevantTerms r.asserted) (freeConsts as) (engineDefs as opts preprocess order) as
      r.arithModel r.asserted
    if accepts M as opts preprocess order then { r with model := some M }
    else rejectModel r (rejectionWhy sc.dtNames r M as out)
  return (out, r)

/-- Why the answer is `unknown`, with its code (`[code] detail`): it was not
certified, or the solver did not decide it. -/
def unknownReason (r : Solver.Result) : Option String :=
  if r.answer != .unknown then none else
  match r.why with
  | some w => some s!"unknown {w.message}"
  | none => some "unknown [internal] no reason recorded"

/-- Solve the script and give only its answer (no events are recorded), and
why an answer was not certified, if it was not. -/
def solveAnswer (sc : Script) (u : Preprocess.UserOptions := {}) (viaSat : Bool := false) :
    Except String (Solver.Answer × Option String) := do
  let (_, r) ← solveScript sc u (viaSat := viaSat) (events := false)
  return (r.answer, unknownReason r)

/-- **The solver**: the answer of `telos --solve` on the script `sc`, with the
user's options `u` (and `viaSat`: the SAT solver even for a conjunction of
literals). The answer of `solveAnswer`, which also says why it is `unknown`. -/
def solve (sc : Script) (u : Preprocess.UserOptions := {}) (viaSat : Bool := false) :
    Except String Solver.Answer :=
  (solveAnswer sc u viaSat).map (·.1)

/-- Preprocess `sc`, solve the result if it is a conjunction of literals, and
print the events and the answer; also why an `unsat` of the engine was not
certified, if it was not (the answer is then `unknown`), and with `withProof`
the CPC refutation of the literals of a certified `unsat`
(`Telos/Solver/EqProofCpc.lean`), whose skolems are their CPC terms. Skolems
are printed as `--post-asserts` names them in the events. -/
def theoryEvents (sc : Script) (u : Preprocess.UserOptions := {}) (eeEvents : Bool := false)
    (preprocess : Bool := true) (withProof : Bool := false) (cvc5Order : Bool := true)
    (viaSat : Bool := false) (triggerEvents : Bool := false) :
    Except String (String × Option String × Option (Except String String)) := do
  let (out, r) ← solveScript sc u eeEvents preprocess withProof cvc5Order viaSat triggerEvents
  -- the skolems of the input, then those that lemmas introduced
  let σ := (namedSkolems sc.dtNames (out ++ r.events.toList.flatMap Event.nodes)).map fun (k, v, _) => (k, v)
  let lines := (r.events.toList.map fun e => (e.map (substSkolems σ)).print sc.dtNames).filter (· != "")
  let proof := if !withProof then none else
    match r.cert with
    | some (A, p) => some (renderRefutation sc.names sc.decls A p)
    | none => none
  let note := match r.why with
    | some w => if r.answer == .unknown && w.code != "needs-sat" then some s!"unknown {w.message}" else none
    | none => if r.byCertificate then some "unsat by certificate (the verified explanation did not apply)" else none
  return ("\n".intercalate (lines ++ [r.answer.name]) ++ "\n", note, proof)

end Telos.Frontend
