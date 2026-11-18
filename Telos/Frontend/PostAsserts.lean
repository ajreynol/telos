import Telos.Frontend.Script
import Telos.Preprocess.Preprocess

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

Deviations from cvc5: `define-fun`s are macros, expanded when the script is
read, so they are not printed, nor are the `(assert true)` that cvc5 keeps in
their place.
-/

namespace Telos.Frontend

/-- The symbols of an SMT-LIB text: its tokens other than parentheses. -/
def tokens (s : String) : List String :=
  ((s.replace "(" " ").replace ")" " ").splitOn " " |>.filter (!·.isEmpty)

/-- The declarations needed by the texts `ts`: those of the symbols they use,
and of the symbols those declarations use, in the order of `syms`. -/
partial def usedSymbols (syms : List Symbol) (ts : List String) : List Symbol :=
  let rec close (used : List Symbol) (toks : List String) : List Symbol :=
    let new := syms.filter fun s => !used.any (·.decl == s.decl) && s.names.any toks.contains
    if new.isEmpty then used
    else close (used ++ new) (toks ++ new.flatMap (tokens ·.decl))
  let used := close [] (ts.flatMap tokens)
  syms.filter fun s => used.any (·.decl == s.decl)

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

/-- The skolems of the assertions `ns` named as symbols (`@purify_1`, …), and
their declarations. -/
def nameSkolems (N : DtNames) (ns : List Node) : List Node × List String :=
  let ks := (ns.flatMap topSkolems).foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  let named := ks.zipIdx.filterMap fun (k, i) => do
    let .skolem id _ := k | none
    let T ← k.typeHint
    let name := s!"{id.name}_{i + 1}"
    return (k, Node.var name T, declareFun N name T)
  (ns.map (substSkolems (named.map fun (k, v, _) => (k, v))), named.map (·.2.2))

/-- Preprocess the assertions of `sc`, and print the result as cvc5's
`-o post-asserts` does. -/
def postAsserts (sc : Script) : Except String String := do
  let as ← sc.assertions.mapM fun a => match a.node with
    | .ok n =>
      if n.typeHint == some .boolean then pure n
      else throw s!"the assertion is not a well-typed formula: {a.source}"
    | .error e => throw s!"{e}: {a.source}"
  let out := if as.isEmpty then #[] else Preprocess.preprocess as
  let (out, skolemDecls) := nameSkolems sc.dtNames out.toList
  let asserts := out.map fun n => s!"(assert {n.toSmtLibWith sc.dtNames})"
  let decls := usedSymbols sc.symbols asserts
  let isType (s : Symbol) := s.decl.startsWith "(declare-sort" || s.decl.startsWith "(declare-datatype"
  let lines := [";; post-asserts start", s!"(set-logic {sc.logic.getD "ALL"})"] ++
    (decls.filter isType ++ decls.filter (!isType ·)).map (·.decl) ++ skolemDecls ++
    asserts ++ ["(check-sat)", ";; post-asserts end"]
  return "\n".intercalate lines ++ "\n"

end Telos.Frontend
