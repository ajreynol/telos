import Cpc.Api
import Telos.Core.Node.OfEo
import Telos.Core.Node.Print
import Telos.Core.Proof.Eunoia

/-!
# SMT-LIB scripts

Reads an SMT-LIB script of declarations, `(simplify t)` and `(assert t)` commands,
as cvc5 accepts. `Telos/Frontend/Simplify.lean` rewrites each simplified `t`;
`Telos/Frontend/PostAsserts.lean` preprocesses the assertions.

Terms are read by Logos's parser, so they mean exactly what they mean in a CPC
proof. The script is rewritten into a Eunoia input that Logos's parser accepts:
declarations are kept, and `(simplify t)` becomes the assumption
`(assume @sN (= t t))`, from which `t` is taken back. Logos numbers declared
constants and sorts (`UConst i`, `USort i`) in declaration order; the front end
replays that numbering to map constants back to their names, so that they become
`Node.var`s (which `Node.toEo` numbers by name, `constId`).

Supported commands: `declare-const`, `declare-fun`, `declare-sort`,
`declare-datatypes` and `declare-datatype`, `define-fun`, `simplify`, `assert`,
`check-sat` and `set-logic`; `set-option`, `set-info` and `exit` are ignored.
Scripts of `simplify` queries have no assertions; a benchmark for the
preprocessor has assertions and one `check-sat` after them (incremental scripts
are not supported).
Bit-vector numerals `(_ bvN w)` are read as `#b…` literals (`bvNumerals`).
A `define-fun` is a macro, as Eunoia's `define`: its uses are expanded when the
script is read, and it is not recorded.
Everything else is an error. Logos's datatypes have no constructor or selector
names; the front end reads them from the declarations, for printing
(`DtNames`).
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

/-- One `(assert t)` of a script, read back, with defined functions expanded. -/
structure Assertion where
  /-- The term as written. -/
  source : String
  /-- The term as a node, or why it could not be read. -/
  node : Except String Node

/-- A declared symbol: its name and its declaration as cvc5 prints it in a
benchmark (`declare-fun`, `declare-sort`, `declare-datatypes`). A datatype
declaration declares several names. -/
structure Symbol where
  names : List String
  decl : String

/-- A script, read. -/
structure Script where
  /-- The declarations, as written; they head each printed proof. -/
  decls : List String
  names : Eunoia.Names
  queries : List Query
  dtNames : DtNames := {}
  assertions : List Assertion := []
  /-- The logic of `set-logic`. -/
  logic : Option String := none
  /-- The declared sorts, datatypes and constants, in order. -/
  symbols : List Symbol := []

def ignored : List String := ["set-option", "set-info", "exit"]

/-- The SMT-LIB bit-vector numerals `(_ bvN w)` of `s` written as binary
literals `#b…` of width `w`, which Logos's parser reads. -/
partial def bvNumerals : Sexp → Sexp
  | .expr [.atom "_", .atom v, .atom w] =>
    match (if v.startsWith "bv" then (v.drop 2).toString.toNat? else none), w.toNat? with
    | some n, some w =>
      if w == 0 then .expr [.atom "_", .atom v, .atom (toString w)] else
      let bits := (List.range w).reverse.map fun i => if n.testBit i then '1' else '0'
      .atom ("#b" ++ String.ofList bits)
    | _, _ => .expr [.atom "_", .atom v, .atom w]
  | .expr xs => .expr (xs.map bvNumerals)
  | a => a

/-! ## cvc5's numerals

cvc5 prints a constant of type `Real` with an integral value as an integer
numeral (`1`), a negative constant as `(- 1)`, and a non-integral one as
`(/ 3 2)` or `(/ (- 3) 2)`. Read as terms, these are ill typed in CPC next to
reals (`(>= x 1)` for a real `x`), and they are not constants. When reading
cvc5's output (`--no-preprocess`, replay), `cvc5Numerals` writes them as the
literals they denote: `-1` for an integer, `3/2` (with `n/1` for an integral
value) for a real, which Logos's parser reads as constants. -/

/-- The arithmetic type of a term, as far as `cvc5Numerals` needs it. -/
inductive NumTy where
  | int | real | other
  deriving BEq, Inhabited

/-- The arithmetic type named by a sort. -/
def NumTy.ofSort : Sexp → NumTy
  | .atom "Int" => .int
  | .atom "Real" => .real
  | _ => .other

/-- An integer numeral, `n` or `(- n)`. -/
def intLit? : Sexp → Option Int
  | .atom a => if !a.isEmpty && a.all Char.isDigit then a.toNat?.map Int.ofNat else none
  | .expr [.atom "-", .atom a] =>
    if !a.isEmpty && a.all Char.isDigit then a.toNat?.map (- Int.ofNat ·) else none
  | _ => none

/-- A rational literal as cvc5 prints one: an integer numeral, or `(/ a b)` of
integer numerals with `b ≠ 0`. -/
def ratLit? (s : Sexp) : Option Rat :=
  match intLit? s with
  | some i => some i
  | none => match s with
    | .expr [.atom "/", a, b] => do
      let a ← intLit? a
      let b ← intLit? b
      if b == 0 then none else some ((a : Rat) / b)
    | _ => none

/-- The literal of a rational of type `Real`. -/
def realAtom (q : Rat) : Sexp := .atom s!"{q.num}/{q.den}"

/-- The operators whose arguments have one arithmetic type. -/
def arithOps : List String := ["+", "-", "*", "<", "<=", ">", ">=", "=", "distinct", "abs"]

mutual
  /-- The arithmetic type of `s`, for the types `env` of the symbols. -/
  partial def numTy (env : List (String × NumTy)) : Sexp → NumTy
    | .atom a =>
      if !a.isEmpty && a.all Char.isDigit then .int
      else if a.contains '.' || a.contains '/' then .real
      else (env.lookup a).getD .other
    | s@(.expr (.atom h :: args)) =>
      if (ratLit? s).isSome then (if h == "/" then .real else .int)
      else if h == "/" || h == "to_real" then .real
      else if h == "to_int" then .int
      else if h == "ite" then match args with
        | [_, t, e] => let a := numTy env t; if a == .real || numTy env e == .real then .real else a
        | _ => .other
      else if h == "let" then match args with
        | [.expr bs, body] => numTy (letEnv env bs) body
        | _ => .other
      else if h == "!" then match args with
        | t :: _ => numTy env t
        | _ => .other
      else if ["+", "-", "*", "abs"].contains h then
        if args.any (numTy env · == .real) then .real else if args.isEmpty then .other else .int
      else (env.lookup h).getD .other
    | _ => .other
  /-- The symbols bound by a `let`. -/
  partial def letEnv (env : List (String × NumTy)) (bs : List Sexp) : List (String × NumTy) :=
    bs.foldl (fun e b => match b with
      | .expr [.atom x, t] => (x, numTy env t) :: e
      | _ => e) env
end

/-- `s` with its numerals in positions of type `Real` written as real
literals (SMT-LIB reads a numeral there as a real; CPC as an integer); `real`
when `s` is in such a position. With `fold` (cvc5's output), its integer
constants `(- n)` and rational constants `(/ a b)` are written as the literals
they denote too. -/
partial def cvc5Numerals (env : List (String × NumTy)) (fold real : Bool) (s : Sexp) : Sexp :=
  let lit? : Option Rat := if fold then ratLit? s else (intLit? s).map (fun i => (i : Rat))
  match lit? with
  | some q =>
    if real || q.den != 1 then realAtom q
    else if fold then Sexp.atom (toString q.num) else s
  | none =>
    match s with
    | Sexp.expr (Sexp.atom h :: args) =>
      if arithOps.contains h then
        let realArgs := args.any (numTy env · == .real) ||
          (real && ["+", "-", "*", "abs"].contains h)
        Sexp.expr (Sexp.atom h :: args.map (cvc5Numerals env fold realArgs))
      else if h == "/" then Sexp.expr (Sexp.atom h :: args.map (cvc5Numerals env fold true))
      else if h == "to_real" then Sexp.expr (Sexp.atom h :: args.map (cvc5Numerals env fold false))
      else if h == "ite" then match args with
        | [c, t, e] =>
          let r := real || numTy env t == .real || numTy env e == .real
          Sexp.expr [Sexp.atom h, cvc5Numerals env fold false c, cvc5Numerals env fold r t,
            cvc5Numerals env fold r e]
        | _ => Sexp.expr (Sexp.atom h :: args.map (cvc5Numerals env fold false))
      else if h == "let" then match args with
        | [Sexp.expr bs, body] =>
          let bs' := bs.map fun b => match b with
            | Sexp.expr [Sexp.atom x, t] => Sexp.expr [Sexp.atom x, cvc5Numerals env fold false t]
            | b => b
          Sexp.expr [Sexp.atom h, Sexp.expr bs', cvc5Numerals (letEnv env bs) fold real body]
        | _ => Sexp.expr (Sexp.atom h :: args.map (cvc5Numerals env fold false))
      else Sexp.expr (Sexp.atom h :: args.map (cvc5Numerals env fold false))
    | Sexp.expr xs => Sexp.expr (xs.map (cvc5Numerals env fold false))
    | a => a

/-- A declared field type, over the parameters `ps` of a parametric datatype. -/
partial def typeTemplate (ps : List String) : Sexp → TypeTemplate
  | .atom a => match ps.idxOf? a with
    | some k => .param k
    | none => .app a []
  | .expr (.atom h :: args) => .app h (args.map (typeTemplate ps))
  | s => .app s.serialize []

/-- A datatype declaration as read: its constructors, each with its name and
its selectors' names and declared types, and the names of its parameters. -/
structure DtDeclared where
  cons : Array (String × Array (String × Sexp))
  params : List String := []

/-- The names of the constructors and selectors of a declaration. -/
def DtDeclared.consNames (dd : DtDeclared) : List String :=
  dd.cons.toList.flatMap fun (c, ss) => c :: ss.toList.map (·.1)

/-- The constructors of a datatype declaration, `((C (s T) …) …)`, or
`(par (P …) ((C (s T) …) …))` for a parametric one. -/
def readConstructors (cs : Sexp) : Except String DtDeclared := do
  let .expr cs := cs | throw s!"bad datatype constructors: {cs.serialize}"
  let (params, cs) ← match cs with
    | [.atom "par", .expr ps, .expr cs] =>
      pure (← ps.mapM fun | .atom p => pure p | p => throw s!"bad parameter: {p.serialize}", cs)
    | .atom "par" :: _ => throw s!"bad parametric datatype: {(Sexp.expr cs).serialize}"
    | cs => pure ([], cs)
  let cons ← cs.toArray.mapM fun c => match c with
    | .atom c => pure (c, #[])
    | .expr (.atom c :: sels) => do
      let sels ← sels.toArray.mapM fun
        | .expr [.atom s, ty] => pure (s, ty)
        | s => throw s!"bad selector: {s.serialize}"
      pure (c, sels)
    | c => throw s!"bad constructor: {c.serialize}"
  return { cons, params }

/-- The names of datatype constructors and selectors, by datatype, and the
templates of the parametric ones. -/
def mkDtNames (dts : Array (String × DtDeclared)) : DtNames where
  cons d i := (dts.find? (·.1 == d)) >>= fun (_, dd) => dd.cons[i]? |>.map (·.1)
  sel d i j := (dts.find? (·.1 == d)) >>= fun (_, dd) => dd.cons[i]? >>= fun (_, ss) => ss[j]? |>.map (·.1)
  template d := (dts.find? (·.1 == d)) >>= fun (_, dd) =>
    if dd.params.isEmpty then none
    else some (dd.params.length,
      dd.cons.toList.map fun (_, ss) => ss.toList.map fun (_, ty) => typeTemplate dd.params ty)

/-- Renumber the constants the parser numbered in declaration order by their
names (`constId`), as `Node.toEo` numbers them. -/
partial def nameConsts (name : Nat → Option String) : Term → Term
  | .UConst i T =>
    let T := nameConsts name T
    match name i with
    | some s => .UConst (constId s) T
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

/-- Read a script. Numerals in positions of type `Real` are reals
(`cvc5Numerals`). With `cvc5Output`, the script is cvc5's output (its
preprocessed assertions, a replayed trace), whose constants are read as cvc5
prints them. -/
def readScript (input : String) (cvc5Output : Bool := false) : Except String Script := do
  let ss ← Sexp.Parser.manySexps!.run input
  let mut decls := #[]
  let mut eunoia := #[]
  let mut consts : Array String := #[]
  let mut sorts : Array String := #[]
  let mut dts : Array (String × DtDeclared) := #[]
  -- the sources of the `simplify` (`true`) and `assert` (`false`) commands, in order
  let mut items : Array (Bool × String) := #[]
  let mut logic : Option String := none
  let mut symbols : Array Symbol := #[]
  let mut checkSat := false
  -- the arithmetic types of the symbols (of the return types of functions)
  let mut numEnv : List (String × NumTy) := []
  for s in ss do
    let s := bvNumerals s
    let s : Sexp := match s with
      | .expr [.atom "assert", t] => .expr [.atom "assert", cvc5Numerals numEnv cvc5Output false t]
      | .expr [.atom "simplify", t] => .expr [.atom "simplify", cvc5Numerals numEnv cvc5Output false t]
      | s => s
    match s with
    | .expr [.atom "declare-const", .atom x, ty] => numEnv := (x, NumTy.ofSort ty) :: numEnv
    | .expr [.atom "declare-fun", .atom x, _, ret] => numEnv := (x, NumTy.ofSort ret) :: numEnv
    | _ => pure ()
    match s with
    | .expr (.atom c :: _) =>
      if ignored.contains c then continue
      match s with
      | .expr [.atom "set-logic", .atom l] => logic := some l
      | .expr [.atom "check-sat"] => checkSat := true
      | .expr [.atom "declare-const", .atom x, ty] =>
        if ty == .atom "Type" then sorts := sorts.push x else consts := consts.push x
        decls := decls.push s.serialize
        eunoia := eunoia.push s.serialize
        symbols := symbols.push ⟨[x], (Sexp.expr [.atom "declare-fun", .atom x, .expr [], ty]).serialize⟩
      | .expr [.atom "declare-fun", .atom x, .expr args, ret] =>
        consts := consts.push x
        -- Eunoia has no `declare-fun`; a function is a constant of arrow type.
        let ty := if args.isEmpty then ret else .expr (.atom "->" :: args ++ [ret])
        decls := decls.push (Sexp.expr [.atom "declare-const", .atom x, ty]).serialize
        eunoia := eunoia.push s.serialize
        symbols := symbols.push ⟨[x], s.serialize⟩
      | .expr [.atom "declare-sort", .atom x, _] =>
        sorts := sorts.push x
        decls := decls.push s.serialize
        eunoia := eunoia.push s.serialize
        symbols := symbols.push ⟨[x], s.serialize⟩
      | .expr [.atom "declare-datatypes", .expr ds, .expr bodies] =>
        if ds.length != bodies.length then throw s!"bad datatype declaration: {s.serialize}"
        let mut names : List String := []
        for (d, body) in ds.zip bodies do
          match d with
          | .expr [.atom name, .atom _] =>
            let dd ← readConstructors body
            dts := dts.push (name, dd)
            names := names ++ name :: dd.consNames
          | _ => throw s!"bad datatype declaration: {s.serialize}"
        decls := decls.push s.serialize
        eunoia := eunoia.push s.serialize
        symbols := symbols.push ⟨names, s.serialize⟩
      | .expr [.atom "declare-datatype", .atom name, body] =>
        let dd ← readConstructors body
        dts := dts.push (name, dd)
        -- As `declare-datatypes`, which Logos's parser reads.
        let arity := Sexp.atom (toString dd.params.length)
        let s' := Sexp.expr [.atom "declare-datatypes", .expr [.expr [.atom name, arity]], .expr [body]]
        decls := decls.push s'.serialize
        eunoia := eunoia.push s'.serialize
        symbols := symbols.push ⟨name :: dd.consNames, s'.serialize⟩
      -- A macro, as Eunoia's `define` (without the return type).
      | .expr [.atom "define-fun", .atom f, .expr args, _, body] =>
        eunoia := eunoia.push (Sexp.expr [.atom "define", .atom f, .expr args, body]).serialize
      | .expr [.atom "simplify", t] =>
        let t := t.serialize
        eunoia := eunoia.push s!"(assume @s{items.size} (= {t} {t}))"
        items := items.push (true, t)
      | .expr [.atom "assert", t] =>
        if checkSat then throw "incremental scripts are not supported: an assertion after check-sat"
        let t := t.serialize
        eunoia := eunoia.push s!"(assume @s{items.size} {t})"
        items := items.push (false, t)
      | _ => throw s!"unsupported command: {s.serialize}"
    | _ => throw s!"unsupported command: {s.serialize}"
  let (assums, _) ← parseProof ("\n".intercalate eunoia.toList)
  let constName := fun i => consts[i - 1]?
  let dtNames := { mkDtNames dts with sort := fun i => sorts[i - 1]? }
  let names : Eunoia.Names :=
    { sort := fun i => sorts[i - 1]?, dt := dtNames }
  let read := items.toList.zip assums
  let queries := read.filterMap fun ((simp, src), t) =>
    if simp then some ⟨src, toNode constName t⟩ else none
  let assertions := read.filterMap fun ((simp, src), t) =>
    if simp then none
    else some ⟨src, match Node.ofEo [] (nameConsts constName t) with
      | some n => .ok n
      | none => .error "the term uses an operator telos does not support yet"⟩
  return { decls := decls.toList, names, queries, dtNames, assertions, logic,
           symbols := symbols.toList }

end Telos.Frontend
