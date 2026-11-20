import Telos.Frontend.PostAsserts
import Telos.Solver.Engine

/-!
# `--theory-events`: solving conjunctions of literals

Preprocesses a benchmark as `--post-asserts` does, then gives the result to
the theory engine (`Telos/Solver/Engine.lean`) if it is a conjunction of
literals, and prints the engine's events as cvc5 prints them with
`-o theory-events` (`cvc5-theory-events.patch`), then the answer.

The literals are those of the preprocessed assertions, flattened through `and`,
as cvc5's CNF stream asserts the children of a top-level `and` as units. Their
skolems are named as `--post-asserts` names them (`@purify_1`, …), so the
events print them as the post-asserts do.

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

/-- The literals of a conjunction: `true` has none, `and` the literals of its
children; `none` if `n` is not a conjunction of literals. -/
partial def conjLiterals (n : Node) : Option (List Node) :=
  if n == Node.mkTrue then some []
  else match n with
    | .app (.kind .AND) cs => cs.toList.foldlM (fun acc c => (acc ++ ·) <$> conjLiterals c) []
    | .app (.kind .NOT) #[a] => if isConnective a then none else some [n]
    | _ => if isConnective n then none else some [n]

/-- The preprocessed assertions of `sc`, with their skolems named as
`printPostAsserts` names them. -/
def namedAssertions (sc : Script) (out : Array Node) (defs : List Node) : List Node :=
  let rhs := defs.filterMap fun
    | .app (.kind .EQUAL) #[.var .., t] => some t
    | _ => none
  ((nameSkolems sc.dtNames (out.toList ++ rhs)).1).take out.size

/-- Preprocess `sc`, solve the result if it is a conjunction of literals, and
print the events and the answer. -/
def theoryEvents (sc : Script) (u : Preprocess.UserOptions := {}) (eeEvents : Bool := false)
    (preprocess : Bool := true) : Except String String := do
  let logic := sc.logic.getD "ALL"
  let theories ← enabledTheories logic
  let (opts, as) ← ppInput sc u
  let out := if as.isEmpty || !preprocess then as else
    let p := Preprocess.preprocessCert as opts
    namedAssertions sc (Preprocess.Pipeline.assertions p) (Preprocess.Pipeline.defs p)
  let lits ← out.foldlM (fun acc a => match conjLiterals a with
      | some ls => pure (acc ++ ls)
      | none => throw s!"unsupported: the preprocessed assertion {a.toSmtLibLet sc.dtNames} is not a conjunction of literals")
    []
  for l in lits do
    if let .app (.kind .DISTINCT) _ := (atomOf l).1 then
      throw s!"unsupported: the literal {l.toSmtLibLet sc.dtNames} is a distinct"
  let (answer, events) := Solver.run { theories, termBased := opts.termBased, eeEvents } lits
  let lines := events.toList.map (·.print sc.dtNames)
  return "\n".intercalate (lines ++ [answer.name]) ++ "\n"

end Telos.Frontend
