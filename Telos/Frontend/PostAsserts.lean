import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Frontend.Script
import Telos.Core.Node.PrintLet
import Telos.Preprocess.Preprocess
import Telos.Preprocess.ProofExt
import Telos.Core.Proof.Shared

/-!
# `-o post-asserts`

Preprocesses the assertions of a benchmark (`Telos/Preprocess/`) and prints the
result as cvc5 does with `-o post-asserts`: the logic, the declarations the
result uses (sorts and datatypes first, then constants and functions, each in
declaration order), the assertions, and `check-sat`.

Skolems are printed as cvc5 prints them, as declared symbols named after their
identifier (`@purify_1`, `@int_div_by_zero_2`), declared after the other
symbols. cvc5 numbers them in the order it creates them, from a counter it
shares with other internal symbols; telos numbers them from 1 in the order
they occur in the output, so the names agree only up to renaming.

The definitions of the variables that non-clausal simplification solved are
printed as `define-fun`s, as cvc5 prints its top-level substitutions, and the
variables are not declared.

Terms are printed as cvc5 prints them by default (`--dag-thresh=1`), their
shared subterms bound by `let` (`Telos/Core/Node/PrintLet.lean`).

Deviations from cvc5: `define-fun`s are macros, expanded when the script is
read, so they are not printed, nor are the `(assert true)` that cvc5 keeps in
their place.

With a proof (`telos --post-asserts --proof`), the CPC proof of
`(= (and a₁ … aₙ true true) C)` follows, for `aᵢ` the input assertions and `C`
the conjunction of the preprocessed assertions and the definitions (the
pipeline, `Telos/Preprocess/Pipeline.lean`), in which the skolems are their
CPC terms (`(@purify t)` for `@purify_k`). It is built from the pipeline's
certificate after preprocessing (`Proof.emitProof` with
`Preprocess.preprocessExt`), printed with shared terms defined once
(`Proof.renderShared`), and checked by Logos only on request (`check`). The
output does not depend on whether a proof is produced (`postAssertsFull`
computes it from the same pipeline, and the proof only from it).
-/

namespace Telos.Frontend

/-- The symbols of an SMT-LIB text: its tokens other than parentheses. -/
def tokens (s : String) : List String :=
  ((s.replace "(" " ").replace ")" " ").splitOn " " |>.filter (!·.isEmpty)

/-- The declarations needed by the texts `ts`: those of the symbols they use,
and of the symbols those declarations use, in the order of `syms`. Linear in
the size of the texts: the symbols are found by name in a hash map. -/
def usedSymbols (syms : List Symbol) (ts : List String) : List Symbol := Id.run do
  let syms := syms.toArray
  let mut byName : Std.HashMap String (Array Nat) := {}
  for h : i in [0:syms.size] do
    for n in syms[i].names do
      byName := byName.insert n ((byName.getD n #[]).push i)
  let mut usedDecls : Std.HashSet String := {}
  let mut seenToks : Std.HashSet String := {}
  let mut work : Array String := (ts.flatMap tokens).toArray
  while 0 < work.size do
    let t := work.back!
    work := work.pop
    if seenToks.contains t then continue
    seenToks := seenToks.insert t
    for i in byName.getD t #[] do
      let some sym := syms[i]? | continue
      let d := sym.decl
      if !usedDecls.contains d then
        usedDecls := usedDecls.insert d
        work := work ++ (tokens d).toArray
  return syms.toList.filter fun s => usedDecls.contains s.decl

/-- The skolems of `n` that are not inside another skolem, in order of first
occurrence, with repetitions. -/
partial def topSkolems : Node → List Node
  | k@(.skolem ..) => [k]
  | .app op cs =>
    (match op with | .node _ f => topSkolems f | _ => []) ++ cs.toList.flatMap topSkolems
  | _ => []

/-- `n` with each skolem of `σ` replaced by its symbol. -/
partial def substSkolems (σ : List (Node × Node)) : Node → Node
  | k@(.skolem ..) => (σ.lookup k).getD k
  | .app op cs =>
    let op := match op with | .node k f => .node k (substSkolems σ f) | op => op
    .app op (cs.map (substSkolems σ))
  | n => n

/-- The declaration of a symbol of type `T`, a function for an arrow type. -/
def declareFun (N : DtNames) (name : String) (T : TypeNode) : String :=
  let rec args : TypeNode → List TypeNode × TypeNode
    | .function a r => let (as, r) := args r; (a :: as, r)
    | T => ([], T)
  let (as, r) := args T
  s!"(declare-fun {name} ({" ".intercalate (as.map (·.toSmtLibWith N))}) {r.toSmtLibWith N})"

/-- The skolems of the nodes `ns`, each with the symbol that names it
(`@purify_1`, …, numbered in order of first occurrence) and its declaration. -/
def namedSkolems (N : DtNames) (ns : List Node) : List (Node × Node × String) :=
  let ks := (ns.flatMap topSkolems).foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  ks.zipIdx.filterMap fun (k, i) => do
    let .skolem id _ := k | none
    let T ← k.typeHint
    let name := s!"{id.name}_{i + 1}"
    return (k, Node.var name T, declareFun N name T)

/-- The skolems of the assertions `ns` named as symbols (`@purify_1`, …), and
their declarations. -/
def nameSkolems (N : DtNames) (ns : List Node) : List Node × List String :=
  let named := namedSkolems N ns
  (ns.map (substSkolems (named.map fun (k, v, _) => (k, v))), named.map (·.2.2))

/-- The assertions of `sc`, and the preprocessing options for its logic and
the user's options `u`. -/
def ppInput (sc : Script) (u : Preprocess.UserOptions) :
    Except String (Preprocess.PPOptions × List Node) := do
  let logic ← Preprocess.Logic.parse (sc.logic.getD "ALL")
  let opts := Preprocess.PPOptions.ofLogic logic u
  let as ← sc.assertions.mapM fun a => match a.node with
    | .ok n =>
      if n.typeHint == some .boolean then pure n
      else throw s!"the assertion is not a well-typed formula: {a.source}"
    | .error e => throw s!"{e}: {a.source}"
  return (opts, as)

/-- Print the preprocessed assertions `out` and definitions `defs` as cvc5's
`-o post-asserts` does. -/
def printPostAsserts (sc : Script) (out : Array Node) (defs : List Node) : String :=
  -- the definitions `(= x t)`, printed as `define-fun`s; skolems named in both
  let defPairs := defs.filterMap fun
    | .app (.kind .EQUAL) #[.var x T, t] => some (x, T, t)
    | _ => none
  let (named, skolemDecls) := Profile.time "print" (fun _ => "nameSkolems") fun _ =>
    nameSkolems sc.dtNames (out.toList ++ defPairs.map (·.2.2))
  let k := out.size
  let out := named.take k
  let defLines := (defPairs.zip (named.drop k)).map fun ((x, T, _), t) =>
    s!"(define-fun {x} () {T.toSmtLibWith sc.dtNames} {t.toSmtLibLet sc.dtNames})"
  let asserts := Profile.time "print" (fun _ => "assertions") fun _ =>
    out.map fun n => s!"(assert {n.toSmtLibLet sc.dtNames})"
  let defined := defPairs.map (·.1)
  let decls := (Profile.time "print" (fun _ => "usedSymbols") fun _ => usedSymbols sc.symbols (asserts ++ defLines)).filter fun s =>
    !s.names.any defined.contains
  let isType (s : Symbol) := s.decl.startsWith "(declare-sort" || s.decl.startsWith "(declare-datatype"
  let lines := [";; post-asserts start", s!"(set-logic {sc.logic.getD "ALL"})"] ++
    (decls.filter isType ++ decls.filter (!isType ·)).map (·.decl) ++ defLines ++ skolemDecls ++
    asserts ++ ["(check-sat)", ";; post-asserts end"]
  "\n".intercalate lines ++ "\n"

/-- The CPC proof of the preprocessing `p` of the assertions `as`, printed in
parentheses as cvc5's `get-proof` prints a proof; with `check`, first checked
by Logos. -/
def ppProof (sc : Script) (as : List Node) (p : Preprocess.Pipeline (Preprocess.inputNode as))
    (check : Bool) : Except String String := do
  let steps ← Profile.time "proof" (fun _ => "emit") fun _ =>
    Proof.emitProof p (X := Preprocess.preprocessExt)
  if steps.isEmpty then throw "preprocessing did not change the assertions"
  if check then
    let _ ← Profile.time "proof" (fun _ => "check") fun _ =>
      Proof.checkProof steps (eqFormula (Preprocess.inputNode as) p.1)
  let text := Profile.time "proof" (fun _ => "print") fun _ =>
    Proof.renderShared sc.names sc.decls steps (Preprocess.inputNode as) p.1
  return "(\n" ++ text ++ ")\n"

/-- The result of `--post-asserts`: the output, and the proof if requested. -/
structure PPResult where
  output : Except String String
  proof : Option (Except String String) := none

/-- Preprocess the assertions of `sc` and print the result as cvc5's
`-o post-asserts` does, with the user's options `u` and the defaults of the
script's logic (`ALL` if it has none); with `withProof`, also its CPC proof
(checked by Logos with `check`). The output is computed from the pipeline
alone, whatever the other arguments (`postAssertsFull_output`). -/
def postAssertsFull (sc : Script) (u : Preprocess.UserOptions := {}) (withProof check : Bool := false) :
    PPResult :=
  match ppInput sc u with
  | .error e => { output := .error e }
  | .ok (opts, as) =>
    if as.isEmpty then { output := .ok (printPostAsserts sc #[] []) }
    else
      let p := Preprocess.preprocessCert as opts
      { output := .ok (printPostAsserts sc (Preprocess.Pipeline.assertions p) (Preprocess.Pipeline.defs p))
        proof := if withProof then some (ppProof sc as p check) else none }

/-- The output of `--post-asserts`. -/
def postAsserts (sc : Script) (u : Preprocess.UserOptions := {}) : Except String String :=
  (postAssertsFull sc u).output

/-- The output does not depend on whether a proof is produced, or checked. -/
theorem postAssertsFull_output (sc : Script) (u : Preprocess.UserOptions) (b₁ c₁ b₂ c₂ : Bool) :
    (postAssertsFull sc u b₁ c₁).output = (postAssertsFull sc u b₂ c₂).output := by
  unfold postAssertsFull
  split <;> (try split) <;> rfl

end Telos.Frontend
