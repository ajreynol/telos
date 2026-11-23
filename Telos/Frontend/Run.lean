import Telos.Frontend.Solve
import Telos.Frontend.Simplify
import Telos.Frontend.ModelPrint
import Telos.Frontend.FullProof

/-!
# Running a script, as cvc5 does

`telos FILE` runs the commands of the script in order and prints what cvc5
prints for each:
- `check-sat`: the answer (`sat`, `unsat` or `unknown`); with `--dump-models`,
  after `sat`, the model; with `--dump-proofs`, after `unsat`, the proof;
- `get-model`, `get-value`: the model, the values of terms (with model
  generation: `--produce-models`, `--dump-models` or `(set-option
  :produce-models true)`);
- `get-proof`: the CPC proof of the last `unsat` (with proof generation:
  `--produce-proofs`, `--dump-proofs` or `(set-option :produce-proofs true)`),
  from the input assertions to `false`, through preprocessing, the CNF
  translation, the theory lemmas and conflicts, and resolution
  (`Telos/Frontend/FullProof.lean`);
- `simplify`: the rewrite of the term (with `--proof`, its CPC proof);
- `echo`, `get-info` (`:reason-unknown`, `:name`, `:version`, `:authors`).

An error is printed as `(error "…")`, as cvc5 prints one, and the script goes
on; the exit status is then `1`. The script is solved once, at its first
`check-sat` (incremental scripts are not supported: no assertion follows a
`check-sat`). Why an answer is `unknown` is printed on standard error
(`Telos/Solver/Unknown.lean`).

Only the answer is verified (`Telos.Frontend.solve_unsat`, `solve_sat`); the
output around it shows the certificates: the model, which the input
evaluates to true in, and the proof, which Ethos checks.
-/

namespace Telos.Frontend

/-- The options of `telos FILE`. -/
structure RunOptions where
  pp : Preprocess.UserOptions := {}
  viaSat : Bool := false
  produceModels : Bool := false
  produceProofs : Bool := false
  dumpModels : Bool := false
  dumpProofs : Bool := false
  /-- `--proof`: the CPC proof of each `simplify`. -/
  simplifyProofs : Bool := false

/-- What running a script printed: on standard output, on standard error, and
whether there was an error. -/
structure RunOutput where
  out : Array String := #[]
  err : Array String := #[]
  failed : Bool := false

def RunOutput.print (o : RunOutput) (s : String) : RunOutput := { o with out := o.out.push s }
def RunOutput.note (o : RunOutput) (s : String) : RunOutput := { o with err := o.err.push s }
def RunOutput.error (o : RunOutput) (e : String) : RunOutput :=
  { o with out := o.out.push s!"(error \"{e.replace "\"" "\"\""}\")", failed := true }

/-- The value of `:reason-unknown`, as cvc5's (`incomplete` when a theory
declared its incompleteness or a part of cvc5 is not ported, `other`
otherwise). -/
def reasonUnknown (r : Solver.Result) : String :=
  match r.why with
  | some (.intentional ..) | some (.notPorted _) | some (.unsupported _) => "incomplete"
  | _ => "other"

/-- **Run a script**, as cvc5 runs one. -/
def runScript (sc : Script) (o : RunOptions) : RunOutput := Id.run do
  let models := o.produceModels || o.dumpModels || sc.produceModels
  let proofs := o.produceProofs || o.dumpProofs || sc.produceProofs
  let mut res : RunOutput := {}
  -- the result of solving, once
  let mut solved : Option (Except String (List Node × Solver.Result)) := none
  let mut last : Option Solver.Result := none
  for c in sc.commands do
    match c with
    | .checkSat =>
      let s := solved.getD (solveScript sc o.pp (wantProof := proofs) (viaSat := o.viaSat) (events := false))
      solved := some s
      match s with
      | .error e => res := res.error e; last := none
      | .ok (out, r) =>
        last := some r
        res := res.print r.answer.name
        if let some w := unknownReason r then res := res.note s!"telos: {w}"
        if o.dumpModels && r.answer == .sat then
          match r.model with
          | some M => res := res.print (printModel sc M)
          | none => res := res.error "no model"
        if o.dumpProofs && r.answer == .unsat then
          match fullProof sc o.pp out r with
          | .ok p => res := res.print p
          | .error e => res := res.error s!"no proof: {e}"
    | .getModel =>
      if !models then res := res.error "cannot get model unless model generation is enabled (try --produce-models)"
      else match last with
        | some r =>
          match r.answer, r.model with
          | .sat, some M => res := res.print (printModel sc M)
          | _, _ => res := res.error "cannot get model unless after a SAT response"
        | none => res := res.error "cannot get model unless after a SAT response"
    | .getValue ts =>
      if !models then res := res.error "cannot get value unless model generation is enabled (try --produce-models)"
      else match last with
        | some r =>
          match r.answer, r.model with
          | .sat, some M =>
            match printValues sc M ts with
            | .ok s => res := res.print s
            | .error e => res := res.error e
          | _, _ => res := res.error "cannot get value unless after a SAT response"
        | none => res := res.error "cannot get value unless after a SAT response"
    | .getProof =>
      if !proofs then res := res.error "cannot get proof unless proofs are enabled (try --produce-proofs)"
      else match solved, last with
        | some (.ok (out, _)), some r =>
          if r.answer != .unsat then
            res := res.error "cannot get proof unless immediately preceded by UNSAT response"
          else match fullProof sc o.pp out r with
            | .ok p => res := res.print p
            | .error e => res := res.error s!"no proof: {e}"
        | _, _ => res := res.error "cannot get proof unless immediately preceded by UNSAT response"
    | .simplify q =>
      let r := simplify sc q o.simplifyProofs
      match r.output with
      | .ok out => res := res.print out
      | .error e => res := res.error s!"{e}: {q.source}"
      match r.proof with
      | some (.ok text) => res := res.print (text.trimAsciiEnd.toString)
      | some (.error e) => res := res.note s!"telos: no proof for {q.source}: {e}"; res := { res with failed := true }
      | none => pure ()
    | .echo s => res := res.print s
    | .getInfo key =>
      match key with
      | ":reason-unknown" =>
        match last with
        | some r =>
          if r.answer == .unknown then res := res.print s!"(:reason-unknown {reasonUnknown r})"
          else res := res.error "Can't get-info :reason-unknown when the last result wasn't unknown!"
        | none => res := res.error "Can't get-info :reason-unknown when the last result wasn't unknown!"
      | ":name" => res := res.print "(:name \"telos\")"
      | ":authors" => res := res.print "(:authors \"the telos authors\")"
      | ":version" => res := res.print "(:version \"0.1\")"
      | k => res := res.error s!"unsupported get-info key {k}"
    | .unsupported src => res := res.error s!"unsupported command: {src}"
  return res

end Telos.Frontend
