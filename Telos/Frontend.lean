import Telos.Rewrite
import Telos.Proof.Emit
import Cpc.Api
import Telos.Node.Print

/-!
# SMT-LIB front end

Reads an SMT-LIB script of declarations and `(simplify t)` commands, as cvc5
accepts, and rewrites each `t`.

Terms are read by Logos's parser, so they mean exactly what they mean in a CPC
proof. The script is rewritten into a Eunoia input that Logos's parser accepts:
declarations are kept, and `(simplify t)` becomes the assumption
`(assume @sN (= t t))`, from which `t` is taken back. Logos numbers declared
constants and sorts (`UConst i`, `USort i`) in declaration order; the front end
replays that numbering to map them back to their names, so that they become
`Node.var`s.

Supported commands: `declare-const`, `declare-fun`, `declare-sort` and
`simplify`; `set-logic`, `set-option`, `set-info`, `check-sat` and `exit` are
ignored. Everything else is an error.
-/

open Eo
open Logos
open SmtEval

namespace Telos.Frontend

/-- One `(simplify t)` of a script, read back. -/
structure Query where
  /-- The term as written. -/
  source : String
  /-- The term as a node, or why it could not be read. -/
  node : Except String Node

/-- A script, read. -/
structure Script where
  /-- The declarations, as written; they head each printed proof. -/
  decls : List String
  names : Eunoia.Names
  queries : List Query

def ignored : List String := ["set-logic", "set-option", "set-info", "check-sat", "exit"]

/-- Replace each numbered constant by the variable of its name. -/
partial def nameConsts (name : Nat → Option String) : Term → Term
  | .UConst i T =>
    let T := nameConsts name T
    match name i with
    | some s => .Var (.String (native_string_lit s)) T
    | none => .UConst i T
  | .Apply f a => .Apply (nameConsts name f) (nameConsts name a)
  | .Var n T => .Var n (nameConsts name T)
  | .UOp1 op i => .UOp1 op (nameConsts name i)
  | .UOp2 op i j => .UOp2 op (nameConsts name i) (nameConsts name j)
  | .UOp3 op i j k => .UOp3 op (nameConsts name i) (nameConsts name j) (nameConsts name k)
  | t => t

/-- The left-hand side of `(= t t)`. -/
def eqLhs? : Term → Option Term
  | .Apply (.Apply (.UOp UserOp.eq) t) _ => some t
  | _ => none

/-- Read a node from a term of the script. -/
def toNode (name : Nat → Option String) (t : Term) : Except String Node :=
  match eqLhs? t with
  | none => .error "internal error: unexpected assumption"
  | some t =>
    match Node.ofEo [] (nameConsts name t) with
    | some n => .ok n
    | none => .error "the term uses an operator telos does not support yet"

/-- Read a script. -/
def readScript (input : String) : Except String Script := do
  let ss ← Sexp.Parser.manySexps!.run input
  let mut decls := #[]
  let mut eunoia := #[]
  let mut sources := #[]
  let mut consts : Array String := #[]
  let mut sorts : Array String := #[]
  for s in ss do
    match s with
    | .expr (.atom c :: _) =>
      if ignored.contains c then continue
      match s with
      | .expr [.atom "declare-const", .atom x, ty] =>
        if ty == .atom "Type" then sorts := sorts.push x else consts := consts.push x
        decls := decls.push s.serialize
        eunoia := eunoia.push s.serialize
      | .expr [.atom "declare-fun", .atom x, .expr args, ret] =>
        consts := consts.push x
        -- Eunoia has no `declare-fun`; a function is a constant of arrow type.
        let ty := if args.isEmpty then ret else .expr (.atom "->" :: args ++ [ret])
        decls := decls.push (Sexp.expr [.atom "declare-const", .atom x, ty]).serialize
        eunoia := eunoia.push s.serialize
      | .expr [.atom "declare-sort", .atom x, _] =>
        sorts := sorts.push x
        decls := decls.push s.serialize
        eunoia := eunoia.push s.serialize
      | .expr [.atom "simplify", t] =>
        let t := t.serialize
        eunoia := eunoia.push s!"(assume @s{sources.size} (= {t} {t}))"
        sources := sources.push t
      | _ => throw s!"unsupported command: {s.serialize}"
    | _ => throw s!"unsupported command: {s.serialize}"
  let (assums, _) ← parseProof ("\n".intercalate eunoia.toList)
  let constName := fun i => consts[i - 1]?
  let names : Eunoia.Names :=
    { sort := fun i => sorts[i - 1]?, const := constName, isConst := consts.contains }
  let queries := (sources.toList.zip assums).map fun (src, t) => ⟨src, toNode constName t⟩
  return { decls := decls.toList, names, queries }

/-- The result of simplifying one term. -/
structure Result where
  source : String
  /-- The rewritten term, in SMT-LIB syntax, or an error. -/
  output : Except String String
  /-- The CPC proof of the rewrite, in Eunoia syntax, if requested. -/
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
          | .ok .correct => pure text
          | .ok _ => throw "internal error: Logos does not accept the printed proof"
          | .error e => throw s!"internal error: Logos cannot parse the printed proof: {e}")
        else none
      { source := q.source, output := .ok r.1.toSmtLib, proof }

end Telos.Frontend
