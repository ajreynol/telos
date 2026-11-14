import Telos

/-!
# `telos`: a verified SMT rewriter

```
telos [--proof] [--proof-dir DIR] [--profile] FILE
```

Reads an SMT-LIB script of declarations and `(simplify t)` commands (`-` for
standard input) and prints the rewrite of each `t`, as cvc5 does. With `--proof`,
each result is followed by a CPC proof of `(= t result)` in Eunoia syntax; with
`--proof-dir DIR`, the proof of the `i`-th query is written to `DIR/proof-i.eo`
instead. A proof is a refutation of `(not (= t result))`, which Ethos and the
`logos` executable check. telos prints only proofs that Logos's checker accepts.
With `--profile`, a table of where the time went is printed to standard error
(`Telos/Profile.lean`).

Every result is equivalent to its input (`Telos.rewrite_correct`), with or
without proofs.
-/

open Telos Telos.Frontend

structure Options where
  proof : Bool := false
  proofDir : Option String := none
  file : Option String := none
  profile : Bool := false

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--proof" :: rest, o => parseArgs rest { o with proof := true }
  | "--profile" :: rest, o => parseArgs rest { o with profile := true }
  | "--proof-dir" :: d :: rest, o => parseArgs rest { o with proofDir := some d }
  | ["--proof-dir"], _ => .error "--proof-dir needs a directory"
  | f :: rest, o =>
    if f.startsWith "--" && f != "-" then .error s!"unknown option {f}"
    else if o.file.isSome then .error "only one input file is accepted"
    else parseArgs rest { o with file := some f }

def usage : String := "usage: telos [--proof] [--proof-dir DIR] [--profile] FILE"

def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"telos: {e}\n{usage}"; return 2
  let some file := opts.file | IO.eprintln usage; return 2
  let input ← if file == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile file
  let sc ← match readScript input with
    | .ok sc => pure sc
    | .error e => IO.eprintln s!"telos: {e}"; return 1
  if let some d := opts.proofDir then IO.FS.createDirAll d
  if opts.profile then Profile.enable
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
