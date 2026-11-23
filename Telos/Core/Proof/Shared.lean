import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Proof.Emit
import Telos.Core.Node.OfEo

/-!
# Printing large proofs with shared terms

`CheckedProof.render` prints each term in full, as a tree, which is fine for the
rewriter's proofs but not for the preprocessor's, whose terms are the
assertions: large, and highly shared. `renderShared` prints a proof in time
linear in the size of its terms as DAGs, as cvc5 does: each subterm that occurs
more than once is given a name by a `define`, `(define @t3 () (f a b))`, and
written as its name.

A node is defined when it occurs more than once (counting each distinct parent
once, and each occurrence as a step argument), has children, has a type, and
contains no bound variable (a definition is outside the binders). Its body is
printed with its defined children as their names: the children are replaced by
constants `Term.UConst` of the name, which the printer writes as the name.

The arguments that are Logos terms (those of the rewriter's certified steps,
which `Node.toEo` built as trees) are read back as nodes (`Node.ofEo`) when they
translate back to the same term, so that they are shared too; every node is
interned (`intern`), so that equal subterms are the same in memory and compare
in constant time.

The steps are printed without their conclusions, which the checker computes
(Ethos and Logos accept `(step @p :rule …)`), so printing needs no checking.
The printer is not trusted: whoever reads the proof checks it.
-/

open Eo

namespace Telos.Proof

/-- Whether a node contains a bound variable, memoized. -/
partial def hasBound (n : Node) : StateM (Std.HashMap Key Bool) Bool := do
  if let some b := (← get).get? ⟨n⟩ then return b
  let b ← match n with
    | .boundVar .. => pure true
    | .skolem _ cs => cs.anyM hasBound
    | .app _ cs => cs.anyM hasBound
    | _ => pure false
  modify (·.insert ⟨n⟩ b)
  return b

/-- `n` with equal subterms made the same in memory, by a table of the nodes
seen so far. -/
partial def intern (n : Node) : StateM (Std.HashMap Key Node) Node := do
  if let some m := (← get).get? ⟨n⟩ then return m
  let n' ← match n with
    | .app op cs => pure (.app op (← cs.mapM intern))
    | .skolem id cs => pure (.skolem id (← cs.mapM intern))
    | _ => pure n
  match (← get).get? ⟨n'⟩ with
  | some m => return m
  | none => modify (·.insert ⟨n'⟩ n'); return n'

/-- An argument as an interned node when possible: a node, or a Logos term
that `Node.ofEo` reads back exactly. -/
def internArg (a : PArg) : StateM (Std.HashMap Key Node) PArg := do
  match a with
  | .node n => return .node (← intern n)
  | .term t =>
    match Node.ofEo [] t with
    | some n => if n.toEo == t then return .node (← intern n) else return a
    | none => return a

structure ShareState where
  /-- How many times each node occurs: as a root, or as a child of distinct
  parents. -/
  refs : Std.HashMap Key Nat := {}
  seen : Std.HashSet Key := {}

/-- Count the occurrences of the subterms of `n`, visiting each node once. -/
partial def countRefs (n : Node) : StateM ShareState Unit := do
  modify fun s => { s with refs := s.refs.insert ⟨n⟩ (s.refs.getD ⟨n⟩ 0 + 1) }
  if (← get).seen.contains ⟨n⟩ then return
  modify fun s => { s with seen := s.seen.insert ⟨n⟩ }
  match n with
  | .skolem _ cs | .app _ cs => for c in cs do countRefs c
  | _ => pure ()

structure PrintState where
  /-- The term of each node printed so far: its name, if defined. -/
  terms : Std.HashMap Key Term := {}
  defs : Array String := #[]

/-- The term of `n` for printing, with the defined subterms as their names;
the definitions are added to the state, children first. -/
partial def sharedTerm (N : Eunoia.Names) (refs : Std.HashMap Key Nat)
    (bound : Std.HashMap Key Bool) (n : Node) :
    StateM PrintState Term := do
  if let some t := (← get).terms.get? ⟨n⟩ then return t
  let (cs, rebuild) : Array Node × (List Term → Term) := match n with
    | .skolem id cs => (cs, id.toEo)
    | .app op cs => (cs, op.eoShape.toEo)
    | _ => (#[], fun _ => n.toEo)
  let body ← if cs.isEmpty then pure n.toEo else do
    let ts ← cs.toList.mapM (sharedTerm N refs bound)
    pure (rebuild ts)
  let bnd := bound.getD ⟨n⟩ true
  let t ← match n.typeHint with
    | some T =>
      if !cs.isEmpty && refs.getD ⟨n⟩ 0 ≥ 2 && !bnd then do
        let name := s!"@t{(← get).defs.size + 1}"
        let line := s!"(define {name} () {Eunoia.print N body})"
        modify fun s => { s with defs := s.defs.push line }
        pure (Term.UConst (constId name) T.toEo)
      else pure body
    | none => pure body
  modify fun s => { s with terms := s.terms.insert ⟨n⟩ t }
  return t

/-- Print the proof `steps` of `(= t s)` as Eunoia commands: the given
declarations, the definitions of the shared terms, the assumption
`(not (= t s))`, the steps (without conclusions), and `false` by `contra`. -/
def renderShared (N : Eunoia.Names) (decls : List String) (steps : Array Step) (t s : Node) :
    String := Id.run do
  let ((goal, steps), _) := Profile.time "print" (fun _ => "intern") fun _ => (do
      let g ← intern (Node.mkNode .EQUAL #[t, s])
      let ss ← steps.mapM fun st => do return { st with args := ← st.args.mapM internArg }
      return (g, ss) : StateM (Std.HashMap Key Node) _).run {}
  let roots := #[goal] ++ steps.flatMap fun st => st.args.toArray.filterMap fun
    | .node n => some n
    | .term _ => none
  let ((), sh) := Profile.time "print" (fun _ => "count") fun _ => (roots.forM countRefs).run {}
  let ((), bound) := Profile.time "print" (fun _ => "bound") fun _ =>
    (roots.forM fun r => do let _ ← hasBound r).run {}
  let mut ps : PrintState := {}
  let mut lines : Array String := #[]
  let pr (a : PArg) (ps : PrintState) : String × PrintState :=
    match a with
    | .term x => (Eunoia.print N x, ps)
    | .node n => let (x, ps) := (sharedTerm N sh.refs bound n).run ps; (Eunoia.print N x, ps)
  let name (i : Nat) := s!"@p{i}"
  let (g, ps') := pr (.node goal) ps
  ps := ps'
  for h : i in [0:steps.size] do
    let st := steps[i]
    let prems := if st.premises.isEmpty then ""
      else s!" :premises ({" ".intercalate (st.premises.map name)})"
    let mut args : Array String := #[]
    for a in st.args do
      let (x, ps') := pr a ps
      ps := ps'
      args := args.push x
    let argStr := if args.isEmpty then "" else s!" :args ({" ".intercalate args.toList})"
    lines := lines.push <| match st.kind with
      | .assume => s!"(assume-push {name i} {args[0]?.getD "false"})"
      | .pop => s!"(step-pop {name i} :rule {ruleName st.rule}{prems}{argStr})"
      | .step => s!"(step {name i} :rule {ruleName st.rule}{prems}{argStr})"
  let last := name (steps.size - 1)
  return "\n".intercalate (decls ++ ps.defs.toList ++ [s!"(assume @goal (not {g}))"] ++
    lines.toList ++ [s!"(step @false false :rule contra :premises ({last} @goal))"]) ++ "\n"

/-- Print the proof `steps` of `false` from assumptions as Eunoia commands, as
cvc5's `get-proof` prints a refutation: the given declarations, the definitions
of the shared terms, the first `inputs` steps (whose one argument is a formula)
as `assume`s, the others as steps, the last stating its conclusion, `false`. -/
def renderRefutation (N : Eunoia.Names) (decls : List String) (steps : Array Step) (inputs : Nat) :
    String := Id.run do
  let (steps, _) := (steps.mapM fun st => do return { st with args := ← st.args.mapM internArg } :
      StateM (Std.HashMap Key Node) _).run {}
  let roots := steps.flatMap fun st => st.args.toArray.filterMap fun
    | .node n => some n
    | .term _ => none
  let ((), sh) := (roots.forM countRefs).run {}
  let ((), bound) := (roots.forM fun r => do let _ ← hasBound r).run {}
  let mut ps : PrintState := {}
  let mut lines : Array String := #[]
  let pr (a : PArg) (ps : PrintState) : String × PrintState :=
    match a with
    | .term x => (Eunoia.print N x, ps)
    | .node n => let (x, ps) := (sharedTerm N sh.refs bound n).run ps; (Eunoia.print N x, ps)
  let name (i : Nat) := s!"@p{i}"
  for h : i in [0:steps.size] do
    let st := steps[i]
    let mut args : Array String := #[]
    for a in st.args do
      let (x, ps') := pr a ps
      ps := ps'
      args := args.push x
    if i < inputs then
      lines := lines.push s!"(assume {name i} {args[0]?.getD "true"})"
      continue
    let prems := if st.premises.isEmpty then ""
      else s!" :premises ({" ".intercalate (st.premises.map name)})"
    let argStr := if args.isEmpty then "" else s!" :args ({" ".intercalate args.toList})"
    let concl := if i + 1 == steps.size then " false" else ""
    lines := lines.push <| match st.kind with
      | .assume => s!"(assume-push {name i} {args[0]?.getD "false"})"
      | .pop => s!"(step-pop {name i}{concl} :rule {ruleName st.rule}{prems}{argStr})"
      | .step => s!"(step {name i}{concl} :rule {ruleName st.rule}{prems}{argStr})"
  return "(\n" ++ "\n".intercalate (decls ++ ps.defs.toList ++ lines.toList) ++ "\n)"

end Telos.Proof
