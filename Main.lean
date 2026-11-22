import Telos

/-!
# `telos`: a verified SMT rewriter and preprocessor

```
telos [--proof] [--proof-dir DIR] [--profile] FILE
telos --post-asserts [PREPROCESSING OPTIONS] [--proof [--check-proof]] [--proof-dir DIR] [--profile] FILE
telos --theory-events [--theory-events-ee] [--trigger] [--no-preprocess] [--no-cvc5-order] [--via-sat] [--proof] [--proof-dir DIR] [PREPROCESSING OPTIONS] FILE
telos --replay TRACE [--theory-events-ee] FILE
```

Reads an SMT-LIB script of declarations and `(simplify t)` commands (`-` for
standard input) and prints the rewrite of each `t`, as cvc5 does. With `--proof`,
each result is followed by a CPC proof of `(= t result)` in Eunoia syntax; with
`--proof-dir DIR`, the proof of the `i`-th query is written to `DIR/proof-i.eo`
instead. A proof is a refutation of `(not (= t result))`, in parentheses as
cvc5's `get-proof` prints it; without the outer parentheses it is a Eunoia
file, which Ethos and the `logos` executable check. telos prints only proofs that Logos's checker accepts.
With `--profile`, a table of where the time went is printed to standard error
(`Telos/Core/Profile.lean`).

Every result is equivalent to its input (`Telos.rewrite_correct`), with or
without proofs.

With `--post-asserts`, `FILE` is a benchmark (declarations, assertions and
`check-sat`), and telos prints its assertions after preprocessing, as cvc5 does
with `-o post-asserts` (`Telos/Frontend/PostAsserts.lean`). Their conjunction is
equivalent, with the definitions of the variables solved by non-clausal
simplification, to that of the input assertions (`Telos.preprocess_correct`).
The preprocessing options are cvc5's, with cvc5's defaults for the script's
logic (`Telos/Preprocess/Options.lean`): `--simplification=none|batch`,
`--[no-]arith-rewrite-equalities`, `--[no-]static-learning`,
`--[no-]arith-static-learning` and `--[no-]repeat-simp`. With `--proof`, the
output is followed by a CPC proof that the conjunction of the input assertions
(and `true`, twice) equals that of the output assertions and definitions, with
skolems as their CPC terms; with `--proof-dir DIR`, it is written to
`DIR/proof.eo`. Shared terms are `define`d once. The proof is not checked by
telos unless `--check-proof` is given (by Logos's checker, which is slow on
large proofs); Ethos checks it. The output is the same with or without a proof
(`postAssertsFull_output`; for `simplify`, `simplify_output`).

With `--theory-events`, `FILE` is a benchmark whose preprocessed assertions are
a conjunction of literals. telos solves it with its theory engine and prints
the events at the interface of the theory solvers, as cvc5 prints them with
`-o theory-events` (`cvc5-theory-events.patch`), then the answer
(`Telos/Frontend/Solve.lean`). Other inputs are reported as unsupported. With
`--theory-events-ee`, also the central equality engine's notifications, as
cvc5's `-o theory-events-ee`. With `--trigger`, also the triggers E-matching
makes, as cvc5's `-o trigger`. With `--no-preprocess`, the assertions are given
to the engine as they are (for testing it on cvc5's own preprocessed
assertions). With `--no-cvc5-order`, the engine does not imitate cvc5's order of
nodes, which only decides the form of what it produces (the orientation of
equalities), so its events may differ from cvc5's. An `unsat` answer is certified: the input assertions are
unsatisfiable (`Telos.solve_unsat_correct`); with `--proof` (or `--proof-dir
DIR`, writing `DIR/proof.eo`), its CPC refutation of the literals follows.

With `--replay TRACE`, `FILE` is cvc5's preprocessed form of a benchmark
(`-o post-asserts`) and `TRACE` cvc5's theory events on it (`-o
theory-events`): telos gives its theories the trace's inputs (registrations,
assertions, checks, backtracking, requests for explanations) and prints its
events (`Telos/Frontend/Replay.lean`), for comparison with the trace.
-/

open Telos Telos.Frontend

structure Options where
  proof : Bool := false
  proofDir : Option String := none
  checkProof : Bool := false
  file : Option String := none
  profile : Bool := false
  postAsserts : Bool := false
  theoryEvents : Bool := false
  theoryEventsEE : Bool := false
  triggers : Bool := false
  noPreprocess : Bool := false
  /-- Do not imitate cvc5's order of nodes (`Solver.Config.cvc5Order`). -/
  noCvc5Order : Bool := false
  replay : Option String := none
  /-- Solve a DIMACS file with the SAT solver alone. -/
  dimacs : Bool := false
  /-- Solve with the SAT solver even a conjunction of literals. -/
  viaSat : Bool := false
  pp : Preprocess.UserOptions := {}

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--proof" :: rest, o => parseArgs rest { o with proof := true }
  | "--profile" :: rest, o => parseArgs rest { o with profile := true }
  | "--check-proof" :: rest, o => parseArgs rest { o with checkProof := true }
  | "--post-asserts" :: rest, o => parseArgs rest { o with postAsserts := true }
  | "--theory-events" :: rest, o => parseArgs rest { o with theoryEvents := true }
  | "--theory-events-ee" :: rest, o => parseArgs rest { o with theoryEventsEE := true }
  | "--trigger" :: rest, o => parseArgs rest { o with triggers := true }
  | "--no-preprocess" :: rest, o => parseArgs rest { o with noPreprocess := true }
  | "--via-sat" :: rest, o => parseArgs rest { o with viaSat := true }
  | "--dimacs" :: rest, o => parseArgs rest { o with dimacs := true }
  | "--no-cvc5-order" :: rest, o => parseArgs rest { o with noCvc5Order := true }
  | "--replay" :: t :: rest, o => parseArgs rest { o with replay := some t }
  | ["--replay"], _ => .error "--replay needs a trace file"
  | "--proof-dir" :: d :: rest, o => parseArgs rest { o with proofDir := some d }
  | ["--proof-dir"], _ => .error "--proof-dir needs a directory"
  | f :: rest, o =>
    if let some pp := o.pp.parseArg f then parseArgs rest { o with pp }
    else if f.startsWith "--" && f != "-" then .error s!"unknown option {f}"
    else if o.file.isSome then .error "only one input file is accepted"
    else parseArgs rest { o with file := some f }

def usage : String :=
  "usage: telos [--proof] [--proof-dir DIR] [--profile] FILE\n       telos --post-asserts [PREPROCESSING OPTIONS] [--proof [--check-proof]] [--proof-dir DIR] [--profile] FILE\n       telos --theory-events [--theory-events-ee] [--trigger] [--no-preprocess] [--no-cvc5-order] [--proof] [--proof-dir DIR] [PREPROCESSING OPTIONS] FILE\n       telos --replay TRACE [--theory-events-ee] FILE\n       telos --dimacs FILE"

def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"telos: {e}\n{usage}"; return 2
  let some file := opts.file | IO.eprintln usage; return 2
  let input ← if file == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile file
  if opts.profile then Profile.enable
  if opts.dimacs then
    match Sat.solveDimacs input with
    | .ok out => IO.println out; return 0
    | .error e => IO.eprintln s!"telos: {e}"; return 1
  let sc ← match ← Profile.measure "frontend" "parse script" fun _ => readScript input (cvc5Output := opts.noPreprocess) with
    | .ok sc => pure sc
    | .error e => IO.eprintln s!"telos: {e}"; return 1
  if let some t := opts.replay then
    let trace ← IO.FS.readFile t
    match replayScript input trace opts.theoryEventsEE with
    | .ok (out, unverified) =>
      IO.print out
      if unverified > 0 then IO.eprintln s!"telos: {unverified} explanations not by the verified explanation"
      if opts.profile then Profile.report
      return 0
    | .error e => IO.eprintln s!"telos: {e}"; return 1
  if opts.theoryEvents then
    let withProof := opts.proof || opts.proofDir.isSome
    match theoryEvents sc opts.pp opts.theoryEventsEE (!opts.noPreprocess) withProof (!opts.noCvc5Order) opts.viaSat opts.triggers with
    | .ok (out, unc, proof) =>
      IO.print out
      if let some e := unc then IO.eprintln s!"telos: {e}"
      match proof with
      | some (.ok text) =>
        match opts.proofDir with
        | some d => IO.FS.createDirAll d; IO.FS.writeFile s!"{d}/proof.eo" text
        | none => IO.print text
      | some (.error e) => IO.eprintln s!"telos: no proof: {e}"; return 1
      | none => pure ()
      if opts.profile then Profile.report
      return 0
    | .error e => IO.eprintln s!"telos: {e}"; return 1
  if opts.postAsserts then
    let withProof := opts.proof || opts.proofDir.isSome
    let r := postAssertsFull sc opts.pp withProof opts.checkProof
    let out ← Profile.measure "total" "preprocess" fun _ => r.output
    match out with
    | .ok out => IO.print out
    | .error e => IO.eprintln s!"telos: {e}"; return 1
    let mut status : UInt32 := 0
    match ← Profile.measure "total" "proof" fun _ => r.proof with
    | some (.ok text) =>
      match opts.proofDir with
      | some d => IO.FS.createDirAll d; IO.FS.writeFile s!"{d}/proof.eo" text
      | none => IO.print text
    | some (.error e) => IO.eprintln s!"telos: no proof: {e}"; status := 1
    | none => pure ()
    if opts.profile then Profile.report
    return status
  if let some d := opts.proofDir then IO.FS.createDirAll d
  let mut status : UInt32 := 0
  for (q, i) in sc.queries.zipIdx do
    let r ← Profile.measure "total" "simplify" fun _ => simplify sc q (opts.proof || opts.proofDir.isSome)
    match r.output with
    | .ok out => IO.println out
    | .error e =>
      IO.println s!"(error \"{e}: {q.source}\")"
      status := 1
    match r.proof with
    | some (.ok text) =>
      match opts.proofDir with
      | some d => IO.FS.writeFile s!"{d}/proof-{i}.eo" text
      | none => IO.print text
    | some (.error e) =>
      IO.eprintln s!"telos: no proof for {q.source}: {e}"
      status := 1
    | none => pure ()
  if opts.profile then Profile.report
  return status
