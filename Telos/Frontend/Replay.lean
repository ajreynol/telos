import Telos.Frontend.PostAsserts
import Telos.Solver.Engine

/-!
# `--replay`: the theories on cvc5's SAT search

`telos --replay TRACE FILE` reads a trace of cvc5's theory events
(`-o theory-events`, `cvc5-theory-events.patch`) of the benchmark `FILE`, which
is cvc5's preprocessed form of the input (`-o post-asserts`, so that the terms
of the trace are its terms). It gives telos's theories the trace's inputs, in
order (`Solver.replay`):
- `(prereg k t)`: register the atom;
- `(assert k T lit)`: assign and assert the literal;
- `(check k T effort)`: run the theory's check;
- `(pop k)`: backtrack to level `k` (pushes are implicit, in the levels);
- `(explain k lit exp)`: explain the propagated literal (the explanation is
  telos's own).

It prints telos's events, which `scripts/fuzz-solve.py --replay` compares with
the trace. So the theories are compared with cvc5's on inputs with SAT
structure, decisions and backtracking, without a SAT solver: the SAT
solver's choices are cvc5's.

The events of the theories outside safe mode, which telos does not model, are
skipped. There is no answer: it is the SAT solver's.
-/

open Logos

namespace Telos.Frontend

open Solver

def theoryOfName (s : String) : Option Theory := Theory.all.find? (·.name == s)

def effortOfName : String → Option Effort
  | "EFFORT_STANDARD" => some .standard
  | "EFFORT_FULL" => some .full
  | "EFFORT_LAST_CALL" => some .lastCall
  | _ => none

/-- An input of the trace, with the index of its term among the terms read. -/
inductive RawInput where
  | prereg (k : Nat) (t : Nat)
  | assert (k : Nat) (T : Theory) (t : Nat)
  | check (k : Nat) (T : Theory) (e : Effort)
  | pop (k : Nat)
  | explain (k : Nat) (t : Nat)

/-- The inputs of a trace, and the terms they mention, as text. -/
def readTrace (trace : String) : Except String (Array RawInput × Array String) := do
  let mut inputs : Array RawInput := #[]
  let mut terms : Array String := #[]
  for line in trace.splitOn "\n" do
    let line := line.trimAscii.toString
    if !line.startsWith "(" then continue
    let kind := ((line.drop 1).takeWhile (· != ' ')).toString
    if !["prereg", "assert", "check", "pop", "explain"].contains kind then continue
    let ss ← Sexp.Parser.manySexps!.run line
    let some (Sexp.expr items) := ss.head? | throw s!"bad trace line: {line}"
    let level (i : Nat) : Except String Nat := match items[i]? with
      | some (Sexp.atom a) => match a.toNat? with
        | some n => .ok n
        | none => .error s!"bad level in: {line}"
      | _ => .error s!"bad trace line: {line}"
    let term (i : Nat) : Except String String := match items[i]? with
      | some t => .ok t.serialize
      | none => .error s!"bad trace line: {line}"
    match kind with
    | "prereg" =>
      inputs := inputs.push (.prereg (← level 1) terms.size)
      terms := terms.push (← term 2)
    | "assert" =>
      let some (Sexp.atom T) := items[2]? | throw s!"bad trace line: {line}"
      -- a theory outside safe mode is not modelled
      let some th := theoryOfName T | continue
      inputs := inputs.push (.assert (← level 1) th terms.size)
      terms := terms.push (← term 3)
    | "check" =>
      let some (Sexp.atom T) := items[2]? | throw s!"bad trace line: {line}"
      let some (Sexp.atom e) := items[3]? | throw s!"bad trace line: {line}"
      let some T := theoryOfName T | continue
      let some e := effortOfName e | throw s!"bad effort in: {line}"
      inputs := inputs.push (.check (← level 1) T e)
    | "pop" => inputs := inputs.push (.pop (← level 1))
    | _ =>
      inputs := inputs.push (.explain (← level 1) terms.size)
      terms := terms.push (← term 2)
  return (inputs, terms)

/-- An s-expression with its `let`s expanded. -/
partial def expandLets (env : List (String × Sexp)) : Sexp → Sexp
  | .atom a => (env.lookup a).getD (.atom a)
  | .expr [.atom "let", .expr binds, body] =>
    let env' := binds.foldl (fun e b => match b with
      | .expr [.atom n, v] => (n, expandLets env v) :: e
      | _ => e) env
    expandLets env' body
  | .expr xs => .expr (xs.map (expandLets env))

/-- The purification skolems that cvc5's theories introduced, from the trace's
purification lemmas `(= @purify_k t)`: their names and the text of their terms,
in order. -/
def purifyDefs (trace : String) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  for line in trace.splitOn "\n" do
    let line := line.trimAscii.toString
    if !line.startsWith "(lemma " || !(line.splitOn "_PURIFY ").length > 1 then continue
    let .ok ss := Sexp.Parser.manySexps!.run line | continue
    let some (Sexp.expr items) := ss.head? | continue
    let some f := items[4]? | continue
    match expandLets [] f with
    | .expr [.atom "=", .atom k, t] =>
      if !(out.any (·.1 == k)) then out := out ++ [(k, t.serialize)]
    | _ => pure ()
  -- a purification whose lemma was dropped (pending in a conflict) shows in the
  -- instantiation of its term `t`: `(= t (C (s₁ k) …))`
  for line in trace.splitOn "\n" do
    let line := line.trimAscii.toString
    if !line.startsWith "(lemma " || !(line.splitOn "_INST ").length > 1 then continue
    let .ok ss := Sexp.Parser.manySexps!.run line | continue
    let some (Sexp.expr items) := ss.head? | continue
    let some f := items[4]? | continue
    let eq := match expandLets [] f with
      | .expr [.atom "=>", _, e] => e
      | e => e
    if let .expr [.atom "=", t, .expr (_ :: .expr [_, .atom k] :: _)] := eq then
      if k.startsWith "@purify_" && !(out.any (·.1 == k)) then out := out ++ [(k, t.serialize)]
  return out

/-- `n` with each free constant named in `σ` replaced. -/
partial def substVars (σ : List (String × Node)) : Node → Node
  | v@(.var name _) => (σ.lookup name).getD v
  | .app op cs =>
    let op := match op with | .node k f => .node k (substVars σ f) | op => op
    .app op (cs.map (substVars σ))
  | .skolem id cs => .skolem id (cs.map (substVars σ))
  | n => n

/-- Replay the trace `trace` on the script `input`: telos's events, printed,
and the number of explanations for which the verified one did not apply. -/
def replayScript (input trace : String) (eeEvents : Bool := false) : Except String (String × Nat) := do
  let (raw, terms) ← Profile.time "replay" (fun _ => "read trace") fun _ => readTrace trace
  -- the purification skolems of the theories, declared as constants of their
  -- terms' types, then replaced by telos's skolems for those terms
  let mut decls := ""
  let mut sks : List (String × Node) := []
  for (name, t) in purifyDefs trace do
    if (input.splitOn s!"(declare-fun {name} ").length > 1 then continue
    let sc ← readScript (input ++ "\n" ++ decls ++ s!"(simplify {t})\n") (cvc5Output := true)
    let some q := sc.queries.getLast? | throw s!"bad purification lemma for {name}"
    let n ← q.node
    let some T := n.typeHint | throw s!"no type for {name}"
    decls := decls ++ declareFun sc.dtNames name T ++ "\n"
    sks := sks ++ [(name, .skolem .PURIFY #[substVars sks n])]
  -- the terms of the trace, read as `simplify` queries of the script
  let text := input ++ "\n" ++ decls ++ "\n".intercalate (terms.toList.map fun t => s!"(simplify {t})") ++ "\n"
  let sc ← Profile.time "replay" (fun _ => "parse terms") fun _ => readScript text (cvc5Output := true)
  let nodes ← Profile.time "replay" (fun _ => "terms to nodes") fun _ => sc.queries.toArray.mapM fun q => q.node
  let nodes := if sks.isEmpty then nodes else nodes.map (substVars sks)
  -- telos's skolems printed with cvc5's names
  let names : List (Node × Node) := sks.filterMap fun (name, k) =>
    (k.typeHint).map fun T => (k, Node.var name T)
  let node (i : Nat) : Except String Node :=
    match nodes[i]? with
    | some n => .ok n
    | none => .error "a term of the trace was not read"
  let theories ← enabledTheories (sc.logic.getD "ALL")
  let (opts, _) ← ppInput sc {}
  let inputs ← raw.toList.mapM fun
    | .prereg k t => return Input.prereg k (← node t)
    | .assert k T t => return Input.assert k T (← node t)
    | .check k T e => return Input.check k T e
    | .pop k => return Input.pop k
    | .explain k t => return Input.explain k (← node t)
  let (events, unverified) := Profile.time "replay" (fun _ => "engine") fun _ =>
    replay { theories, termBased := opts.termBased, eeEvents } inputs
  let text := Profile.time "replay" (fun _ => "print events") fun _ =>
    String.join (events.toList.map fun e => (e.map (substSkolems names)).print sc.dtNames ++ "\n")
  return (text, unverified)

end Telos.Frontend
