import Telos.Solver.Model
import Telos.Frontend.Script

/-!
# Printing models, as cvc5 does

The model of a `sat` answer (`Telos/Solver/Model.lean`), printed as cvc5's
`get-model` and `--dump-models` print it:

```
(
; cardinality of U is 2
; rep: (as @U_0 U)
; rep: (as @U_1 U)
(define-fun u () U (as @U_0 U))
(define-fun x () Int (- 4))
(define-fun r () Real (/ 1 2))
(define-fun f ((_arg_1 Int) (_arg_2 Bool)) Int (ite (= _arg_1 0) (ite _arg_2 3 (- 4)) (- 4)))
)
```

The declared symbols are printed in declaration order: for an uninterpreted
sort, its cardinality in the model and its values; for a constant or a
function, its value, as a `define-fun`. A function's value is its table, as
nested `ite`s over its arguments, one argument at a time (Logos's functions are
curried). Values are printed against their types, so that a nullary
constructor of a parametric datatype is `(as nil (List Int))`. A symbol the
model has no value for (one that the input does not constrain) has the default
value of its type. `get-value` prints `((t v) …)`.

Printing is not verified: the model is certified by evaluating the input in it
(`Model.satisfies`), and printing only shows it.
-/

open Eo Smtm SmtEval

namespace Telos.Frontend

open Solver

/-- An integer, as SMT-LIB writes it: `(- n)` for a negative one. -/
def intStr (i : Int) : String := if i < 0 then s!"(- {-i})" else toString i

/-- A real, as cvc5 prints it: `2.0`, `(- 2.0)`, `(/ 1 2)`, `(/ (- 1) 2)`. -/
def ratStr (q : Rat) : String :=
  if q.den == 1 then (if q.num < 0 then s!"(- {-q.num}.0)" else s!"{q.num}.0")
  else s!"(/ {intStr q.num} {q.den})"

def hexDigits (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList ds

/-- A string literal, as cvc5 prints it: `"` doubled, characters outside the
printable ASCII range (and `\`) as `\u{…}`. -/
def strLit (w : List Nat) : String :=
  "\"" ++ String.join (w.map fun c =>
    if c == 34 then "\"\""
    else if 32 ≤ c && c ≤ 126 && c != 92 then (Char.ofNat c).toString
    else s!"\\u\{{hexDigits c}}") ++ "\""

/-- A regular expression value. -/
def reStr : TRe → String
  | .empty => "re.none"
  | .epsilon => "(str.to_re \"\")"
  | .char c => s!"(str.to_re {strLit [c]})"
  | .range a b => s!"(re.range {strLit [a]} {strLit [b]})"
  | .allchar => "re.allchar"
  | .concat a b => s!"(re.++ {reStr a} {reStr b})"
  | .union a b => s!"(re.union {reStr a} {reStr b})"
  | .inter a b => s!"(re.inter {reStr a} {reStr b})"
  | .star a => s!"(re.* {reStr a})"
  | .comp a => s!"(re.comp {reStr a})"

/-- The name of the value `i` of the uninterpreted sort named `U`. -/
def uvalName (U : String) (i : Nat) : String := s!"(as @{U}_{i} {U})"

structure PrintCtx where
  N : DtNames
  M : Model
  /-- The number of a value of an uninterpreted sort, as printed: cvc5's
  values of a sort are `@U_0`, `@U_1`, …, in order. -/
  uIdx : Nat → Nat → Nat := fun _ i => i

/-- The argument types and the range of a function type. -/
def funSig : TypeNode → List TypeNode × TypeNode
  | .function a r => let (as, R) := funSig r; (a :: as, R)
  | T => ([], T)

mutual
/-- The value `v` of type `T`, in SMT-LIB syntax, as cvc5 prints values. -/
partial def valueStr (C : PrintCtx) (T : TypeNode) (v : MVal) : String :=
  match v, T with
  | .bool b, _ => if b then "true" else "false"
  | .int i, .real => ratStr i
  | .int i, _ => intStr i
  | .rat q, _ => ratStr q
  | .str w, _ => strLit w
  | .re r, _ => reStr r
  | .uval s i, T => uvalName (T.toSmtLibWith C.N) (C.uIdx s i)
  | .sempty _, T => s!"(as set.empty {T.toSmtLibWith C.N})"
  | s@(.sins ..), T =>
    let E := match T with
      | .set E => E
      | _ => .boolean
    let es := s.elems.map fun e => s!"(set.singleton {valueStr C E e})"
    match es with
    | [] => s!"(as set.empty {T.toSmtLibWith C.N})"
    | [e] => e
    | es => es.tail.foldl (fun acc e => s!"(set.union {acc} {e})") es.head!
  | v@(.dtc ..), T | v@(.app ..), T =>
    match v.head with
    | .dtc _ _ i =>
      let fields := (T.dtFields? i).getD []
      let args := (List.range fields.length).filterMap fun k => v.argNth k fields.length
      let name := C.N.consName T i
      if args.isEmpty then
        if C.N.isParametric T then s!"(as {name} {T.toSmtLibWith C.N})" else name
      else
        "(" ++ " ".intercalate (name :: (fields.zip args).map fun (F, a) => valueStr C F a) ++ ")"
    | _ => "?"
  | .fn fid _ _, T =>
    -- a function value, as a lambda of its table
    let (args, R) := funSig T
    let vars := (List.range args.length).map fun k => s!"_arg_{k + 1}"
    s!"(lambda ({" ".intercalate ((vars.zip args).map fun (x, A) => s!"({x} {A.toSmtLibWith C.N})")}) {funBody C (args.zip vars) R (.fn fid .None .None)})"


/-- The body of a function's `define-fun`: its table on the arguments `xs`
(each with its type and variable), as nested `ite`s, cvc5's form. -/
partial def funBody (C : PrintCtx) (xs : List (TypeNode × String)) (R : TypeNode) (v : MVal) : String :=
  match xs, v with
  | [], v => valueStr C R v
  | (A, x) :: rest, .fn fid _ _ =>
    match C.M.funs[fid]? with
    | none => "?"
    | some tbl =>
      let deflt := funBody C rest R tbl.default
      tbl.entries.reverse.foldl (init := deflt) fun acc (a, b) =>
        let cond := match A, a with
          | .boolean, .bool true => x
          | .boolean, .bool false => s!"(not {x})"
          | _, _ => s!"(= {x} {valueStr C A a})"
        s!"(ite {cond} {funBody C rest R b} {acc})"
  | _ :: _, v => valueStr C R v
end

/-- The default value of a type (for a symbol the model has none for). -/
def defaultOf (T : TypeNode) : Option MVal := defaultValue (tyS T)

/-- The values of the uninterpreted sort `s` that occur in the model. -/
partial def uvalsOf (M : Model) (s : Nat) : List Nat :=
  let rec go (v : MVal) : List Nat := match v with
    | .uval s' i => if s' == s then [i] else []
    | .app f a => go f ++ go a
    | .sins e r => go e ++ go r
    | _ => []
  let fromConsts := M.consts.toList.flatMap fun (_, _, v) => go v
  let fromFuns := M.funs.toList.flatMap fun t => go t.default ++ t.entries.flatMap fun (a, b) => go a ++ go b
  (fromConsts ++ fromFuns).foldl (fun acc i => if acc.contains i then acc else acc ++ [i]) [] |>.mergeSort

/-- The `define-fun` of a declared symbol `x` (with its node, for its type). -/
def defineFun (C : PrintCtx) (x : String) (n : Node) : Option String := do
  let T ← n.getType
  let (args, R) := funSig T
  let v := (C.M.const x T).orElse fun _ =>
    if args.isEmpty then defaultOf T else none
  let xs := (List.range args.length).map fun k => s!"_arg_{k + 1}"
  let header := " ".intercalate ((xs.zip args).map fun (y, A) => s!"({y} {A.toSmtLibWith C.N})")
  let body := match v with
    | some v => if args.isEmpty then valueStr C T v else funBody C (args.zip xs) R v
    | none => match defaultOf R with
      | some d => valueStr C R d
      | none => "?"
  return s!"(define-fun {Eunoia.symbol x} ({header}) {R.toSmtLibWith C.N} {body})"

/-- The context of printing the model `M`. -/
def PrintCtx.of (sc : Script) (M : Model) : PrintCtx :=
  { N := sc.dtNames, M, uIdx := fun s i => ((uvalsOf M s).idxOf? i).getD i }

/-- **The model, as cvc5's `get-model` prints it.** -/
def printModel (sc : Script) (M : Model) : String := Id.run do
  let C := PrintCtx.of sc M
  let declared : Std.HashMap String Node := sc.declared.foldl (fun m (x, n) => m.insert x n) {}
  let mut lines : Array String := #["("]
  let mut sortId := 0
  for sym in sc.symbols do
    let isSort := sym.decl.startsWith "(declare-sort"
    if isSort then
      sortId := sortId + 1
      let some U := sym.names.head? | continue
      let vs := uvalsOf M sortId
      let vs := if vs.isEmpty then [0] else vs
      lines := lines.push s!"; cardinality of {U} is {vs.length}"
      for i in vs do lines := lines.push s!"; rep: {uvalName (Eunoia.symbol U) (C.uIdx sortId i)}"
      continue
    if sym.decl.startsWith "(declare-datatype" then continue
    for x in sym.names do
      let some n := declared.get? x | continue
      if let some d := defineFun C x n then lines := lines.push d
  lines := lines.push ")"
  return "\n".intercalate lines.toList

/-- **The values of terms, as cvc5's `get-value` prints them**: `((t v) …)`. -/
def printValues (sc : Script) (M : Model) (ts : List Query) : Except String String := do
  let C := PrintCtx.of sc M
  let mut out : Array String := #[]
  for q in ts do
    let t ← q.node
    let some T := t.getType | throw s!"a term without a type: {q.source}"
    let some v := M.eval t | throw s!"a term the model does not evaluate: {q.source}"
    out := out.push s!"({q.source} {valueStr C T v})"
  return "(" ++ " ".intercalate out.toList ++ ")"

end Telos.Frontend
