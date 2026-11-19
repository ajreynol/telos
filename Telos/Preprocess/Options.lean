/-!
# Preprocessing options

The options of cvc5 that change what the preprocessor does, with their
defaults, which cvc5 sets from the logic (`SetDefaults`,
`src/smt/set_defaults.cpp`) unless the user set them:

* `--simplification=none|batch`: non-clausal simplification (cvc5 turns it off
  for `QF_SAT`, but not with unsat cores, which proofs turn on);
* `--arith-rewrite-equalities`: arithmetic equalities become two inequalities
  in `static-rewrite` (`PreprocessRewriteEq::ppRewriteEq`); on for pure linear
  quantifier-free arithmetic;
* `--static-learning`, `--arith-static-learning`: the `static-learning` pass,
  and arithmetic's part in it;
* `--repeat-simp`: non-clausal simplification again after static learning; on
  for quantifier-free logics with arrays, UF and bit-vectors.

The logic is cvc5's `LogicInfo` (`src/theory/logic_info.cpp`), widened as
`SetDefaults::widenLogic` does: strings add integers, and arrays, datatypes,
sets, non-linear arithmetic, and arithmetic with bit-vectors add UF. telos
matches cvc5 with proofs on (`--produce-proofs`), which also turns on unsat
cores (`unsatCoresMode = SAT_PROOF`): so unconstrained simplification is off
(`SetDefaults::setDefaultsPost` turns it on, and simplification off for
`QF_SAT`, only without unsat cores), and `repeat-simp` follows the logic (it is
off only for `unsatCoresMode = ASSUMPTIONS`).
-/

namespace Telos.Preprocess

/-- A logic, as cvc5's `LogicInfo`, for what the defaults depend on. -/
structure Logic where
  quantified : Bool := false
  uf : Bool := false
  arith : Bool := false
  integers : Bool := false
  reals : Bool := false
  /-- Linear (or difference) arithmetic. -/
  linear : Bool := true
  bv : Bool := false
  arrays : Bool := false
  datatypes : Bool := false
  strings : Bool := false
  sets : Bool := false
  /-- Theories outside telos's scope (floating-point, finite fields, …). -/
  others : Nat := 0
  deriving Repr, BEq

/-- `ALL`. -/
def Logic.all : Logic :=
  { quantified := true, uf := true, arith := true, integers := true, reals := true,
    linear := false, bv := true, arrays := true, datatypes := true, strings := true,
    sets := true, others := 1 }

/-- The theories other than the Booleans and builtins (`d_sharingTheories`). -/
def Logic.numTheories (l : Logic) : Nat :=
  [l.uf, l.arith, l.bv, l.arrays, l.datatypes, l.strings, l.sets].countP id + l.others

/-- `LogicInfo::isPure` of arithmetic: arithmetic and no other theory. -/
def Logic.pureArith (l : Logic) : Bool := l.arith && l.numTheories == 1

/-- The arithmetic theories of logic strings, longest first. -/
private def arithTheories : List (String × Bool × Bool × Bool) :=
  -- name, integers, reals, linear
  [("IRDL", true, true, true), ("LIRA", true, true, true), ("NIRA", true, true, false),
   ("IDL", true, false, true), ("RDL", false, true, true), ("LIA", true, false, true),
   ("LRA", false, true, true), ("NIA", true, false, false), ("NRA", false, true, false)]

/-- `s` without its first `n` characters. -/
private def dropS (s : String) (n : Nat) : String := (s.drop n).toString

/-- The theories after the quantifier prefix (`LogicInfo::setLogicString`). -/
private partial def parseTheories (s : String) (l : Logic) (arithSeen : Bool) :
    Except String Logic := do
  if s.isEmpty then return l
  if s.startsWith "UF" then return ← parseTheories (dropS s 2) { l with uf := true } arithSeen
  if s.startsWith "BV" then return ← parseTheories (dropS s 2) { l with bv := true } arithSeen
  if s.startsWith "DT" then return ← parseTheories (dropS s 2) { l with datatypes := true } arithSeen
  if s.startsWith "FS" then return ← parseTheories (dropS s 2) { l with sets := true } arithSeen
  if s.startsWith "FF" || s.startsWith "FP" then
    return ← parseTheories (dropS s 2) { l with others := l.others + 1 } arithSeen
  if s.startsWith "A" then return ← parseTheories (dropS s 1) { l with arrays := true } arithSeen
  if s.startsWith "S" then return ← parseTheories (dropS s 1) { l with strings := true } arithSeen
  if s.startsWith "C" then return ← parseTheories (dropS s 1) { l with others := l.others + 1 } arithSeen
  match arithTheories.find? (fun (n, _) => s.startsWith n) with
  | some (n, i, r, lin) =>
    if arithSeen then throw s!"more than one arithmetic theory in the logic"
    let rest := dropS s n.length
    -- `NRAT`, `NIRAT`: transcendentals, outside the scope
    let (rest, o) := if !lin && rest.startsWith "T" then (dropS rest 1, 1) else (rest, 0)
    let l' : Logic := { l with arith := true, integers := i, reals := r, linear := lin }
    parseTheories rest { l' with others := l.others + o } true
  | none => throw s!"cannot parse the logic {s}"

/-- `LogicInfo::setLogicString`. -/
def Logic.parse (s : String) : Except String Logic := do
  let s := if s.startsWith "HO_" then dropS s 3 else s
  match s with
  | "" | "QF_SAT" => return {}
  | "SAT" => return { quantified := true }
  | "ALL" | "HORN" => return Logic.all
  | "QF_ALL" => return { Logic.all with quantified := false }
  | _ =>
    let (q, s) := if s.startsWith "QF_" then (false, dropS s 3) else (true, s)
    let (o, s) := if s.startsWith "SEP_" then (1, dropS s 4) else (0, s)
    let l : Logic := { quantified := q, others := o }
    if s.startsWith "AX" then
      if s.length != 2 then throw s!"cannot parse the logic {s}"
      return { l with arrays := true }
    parseTheories s l false

/-- `SetDefaults::widenLogic`, for the theories telos has. -/
def Logic.widen (l : Logic) : Logic :=
  let l := if l.strings then
      { l with arith := true, integers := true,
               linear := if l.arith then l.linear else true } else l
  if l.arrays || l.datatypes || l.sets || (l.arith && !l.linear) || (l.arith && l.bv)
  then { l with uf := true } else l

/-- The options as the user set them (`none`: not set). -/
structure UserOptions where
  simplification : Option Bool := none
  arithRewriteEq : Option Bool := none
  staticLearning : Option Bool := none
  arithStaticLearning : Option Bool := none
  repeatSimp : Option Bool := none
  deriving Repr

/-- The options the preprocessor runs with. -/
structure PPOptions where
  simplification : Bool := true
  arithRewriteEq : Bool := false
  staticLearning : Bool := true
  arithStaticLearning : Bool := true
  repeatSimp : Bool := false
  deriving Repr, BEq

/-- `SetDefaults::setDefaults`: the user's options, and the logic's defaults
for the others. -/
def PPOptions.ofLogic (logic : Logic) (u : UserOptions := {}) : PPOptions :=
  let l := logic.widen
  { simplification := u.simplification.getD true
    arithRewriteEq := u.arithRewriteEq.getD (l.pureArith && l.linear && !l.quantified)
    staticLearning := u.staticLearning.getD true
    arithStaticLearning := u.arithStaticLearning.getD true
    repeatSimp := u.repeatSimp.getD (!l.quantified && l.arrays && l.uf && l.bv) }

/-- A Boolean option of cvc5's command line (`--name`, `--no-name`,
`--name=true|false`) with the name `name`, if `arg` is one. -/
def boolOption? (name arg : String) : Option Bool :=
  if arg == s!"--{name}" || arg == s!"--{name}=true" then some true
  else if arg == s!"--no-{name}" || arg == s!"--{name}=false" then some false
  else none

/-- The user option `arg`, if it is one of the preprocessor's. -/
def UserOptions.parseArg (u : UserOptions) (arg : String) : Option UserOptions :=
  if arg == "--simplification=none" then some { u with simplification := some false }
  else if arg == "--simplification=batch" then some { u with simplification := some true }
  else if let some b := boolOption? "arith-rewrite-equalities" arg then
    some { u with arithRewriteEq := some b }
  else if let some b := boolOption? "static-learning" arg then
    some { u with staticLearning := some b }
  else if let some b := boolOption? "arith-static-learning" arg then
    some { u with arithStaticLearning := some b }
  else if let some b := boolOption? "repeat-simp" arg then
    some { u with repeatSimp := some b }
  else none

end Telos.Preprocess
