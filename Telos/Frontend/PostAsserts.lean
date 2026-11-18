import Telos.Frontend.Script
import Telos.Preprocess.Preprocess

/-!
# `-o post-asserts`

Preprocesses the assertions of a benchmark (`Telos/Preprocess/`) and prints the
result as cvc5 does with `-o post-asserts`: the logic, the declarations the
result uses (sorts and datatypes first, then constants and functions, each in
declaration order), the assertions, and `check-sat`.

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

/-- Preprocess the assertions of `sc`, and print the result as cvc5's
`-o post-asserts` does. -/
def postAsserts (sc : Script) : Except String String := do
  let as ← sc.assertions.mapM fun a => match a.node with
    | .ok n =>
      if n.typeHint == some .boolean then pure n
      else throw s!"the assertion is not a well-typed formula: {a.source}"
    | .error e => throw s!"{e}: {a.source}"
  let out := if as.isEmpty then #[] else Preprocess.preprocess as
  let asserts := out.toList.map fun n => s!"(assert {n.toSmtLibWith sc.dtNames})"
  let decls := usedSymbols sc.symbols asserts
  let isType (s : Symbol) := s.decl.startsWith "(declare-sort" || s.decl.startsWith "(declare-datatype"
  let lines := [";; post-asserts start", s!"(set-logic {sc.logic.getD "ALL"})"] ++
    (decls.filter isType ++ decls.filter (!isType ·)).map (·.decl) ++
    asserts ++ ["(check-sat)", ";; post-asserts end"]
  return "\n".intercalate lines ++ "\n"

end Telos.Frontend
