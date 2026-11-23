import Cpc.Api
import Telos.Core.Node.OfEo
import Telos.Core.Node.Print
import Telos.Core.Node.Key
import Telos.Core.Proof.Eunoia
import Telos.Core.Node.SmtTypeFast

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
`check-sat` and `set-logic`; of `set-option`, only `:decision`; `set-info`
and `exit` are ignored.
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

/-- What an item of the script read by Logos's parser is (`readScript`). -/
inductive ItemKind where
  | assert
  | simplify
  /-- A term of a `get-value`. -/
  | value
  /-- A declared constant or function, read back for its type. -/
  | decl
  deriving BEq, Inhabited

/-- A command of a script that produces output, in order (`telos FILE` runs
them as cvc5 does: `Telos/Frontend/Run.lean`). -/
inductive Command where
  | checkSat
  | getModel
  | getProof
  /-- `(get-value (t₁ … tₙ))`: the terms, read back. -/
  | getValue (terms : List Query)
  | simplify (q : Query)
  | echo (s : String)
  | getInfo (key : String)
  /-- A command telos does not support, with its source: an error when run. -/
  | unsupported (src : String)
  deriving Inhabited

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
  /-- The decision mode of `(set-option :decision MODE)`, if any. -/
  decision : Option String := none
  /-- The declared sorts, datatypes and constants, in order. -/
  symbols : List Symbol := []
  /-- The declared constants and functions, read back: their names and nodes
  (`Node.var`, with their types), in order. -/
  declared : List (String × Node) := []
  /-- The commands that produce output, in order. -/
  commands : List Command := []
  /-- `(set-option :produce-models true)`. -/
  produceModels : Bool := false
  /-- `(set-option :produce-proofs true)`. -/
  produceProofs : Bool := false

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

/-! ### Annotations of quantifiers

Logos's parser has no attributes (`!`: CPC has no patterns). An annotated
quantifier `(forall bs (! body :pattern (p₁ … pₙ) :no-pattern t :qid n))` is
read without its annotation, and its annotation is read on the side: the
quantifier and each term of its annotation are read as assumptions of their
own, in the binders and `let`s around the quantifier (`Frame`), then put back
on the quantifier's node as its pattern list (`INST_PATTERN_LIST`). A `:named`
term is read as its term. -/

/-- A binder or `let` around a subterm. -/
inductive Frame where
  | binder (head : String) (bs : Sexp)
  | lets (bs : Sexp)

/-- `s` in the frames (the innermost first). -/
def wrapFrames (fs : List Frame) (s : Sexp) : Sexp :=
  fs.foldl (fun s f => match f with
    | .binder h bs => .expr [.atom h, bs, s]
    | .lets bs => .expr [.atom "let", bs, s]) s

/-- The number of binders of the frames. -/
def Frame.binders (fs : List Frame) : Nat := (fs.filter fun | .binder .. => true | _ => false).length

/-- An element of an annotation: a pattern, an excluded term, or `:qid`. -/
inductive AnnotElem where
  | pattern (ts : List Sexp)
  | noPattern (t : Sexp)
  | qid (name : String)

/-- An annotated quantifier: its frames, the quantifier without its
annotation, and the annotation. -/
structure Annot where
  /-- The command it is in. -/
  item : Nat := 0
  frames : List Frame
  quant : Sexp
  bs : Sexp
  elems : List AnnotElem

/-- The attributes of a `!`: the annotation's elements, and whether all are
supported. -/
partial def readAttrs : List Sexp → Except String (List AnnotElem)
  | [] => pure []
  | .atom ":pattern" :: .expr ts :: rest => return .pattern ts :: (← readAttrs rest)
  | .atom ":no-pattern" :: t :: rest => return .noPattern t :: (← readAttrs rest)
  | .atom ":qid" :: .atom n :: rest => return .qid n :: (← readAttrs rest)
  | .atom ":named" :: .atom _ :: rest => readAttrs rest
  | a :: _ => throw s!"unsupported attribute: {a.serialize}"

/-- `s` without its annotations, and the annotated quantifiers in it. -/
partial def stripAnnots (fs : List Frame) (s : Sexp) : Except String (Sexp × Array Annot) := do
  match s with
  | .expr [.atom q, bs, body] =>
    if q == "forall" || q == "exists" then
      let fs' := Frame.binder q bs :: fs
      match body with
      | .expr (.atom "!" :: b :: attrs) =>
        let (b', as) ← stripAnnots fs' b
        let elems ← readAttrs attrs
        let quant := Sexp.expr [.atom q, bs, b']
        if elems.isEmpty then return (quant, as)
        return (quant, as.push { frames := fs, quant, bs, elems })
      | _ =>
        let (b', as) ← stripAnnots fs' body
        return (.expr [.atom q, bs, b'], as)
    else if q == "let" then
      let (bs', as₁) ← stripAnnots fs bs
      let (b', as₂) ← stripAnnots (Frame.lets bs :: fs) body
      return (.expr [.atom q, bs', b'], as₁ ++ as₂)
    else
      let (cs, as) ← stripList fs [bs, body]
      return (.expr (.atom q :: cs), as)
  | .expr [.atom "!", t, .atom ":named", .atom _] => stripAnnots fs t
  | .expr (.atom "!" :: _) => throw s!"unsupported annotation: {s.serialize}"
  | .expr cs =>
    let (cs', as) ← stripList fs cs
    return (.expr cs', as)
  | s => return (s, #[])
where
  stripList (fs : List Frame) (cs : List Sexp) : Except String (List Sexp × Array Annot) :=
    cs.foldlM (fun (acc, as) c => do
      let (c', as') ← stripAnnots fs c
      return (acc ++ [c'], as ++ as')) ([], #[])

/-- The assumptions that read an annotation: its quantifier, then each term
of its patterns and excluded terms, each as `(forall bs (= t t))`, in the
frames. -/
def Annot.reads (a : Annot) : List Sexp :=
  let term (t : Sexp) := wrapFrames a.frames (.expr [.atom "forall", a.bs, .expr [.atom "=", t, t]])
  wrapFrames a.frames a.quant :: a.elems.flatMap fun
    | .pattern ts => ts.map term
    | .noPattern t => [term t]
    | .qid _ => []

/-- The node of `t` read in `k` binders: its body below them. -/
def peelBinders : Nat → Node → Node
  | 0, n => n
  | k + 1, n => peelBinders k (n.getChildren[1]?.getD n)

/-- The string constant of a name. -/
def strConst (s : String) : Node := .const (.string (s.toList.map Char.toNat))

/-- The annotated quantifier, from the nodes its assumptions read
(`Annot.reads`): the quantifier, and its pattern list. -/
def Annot.build (a : Annot) (nodes : List Node) : Option (Node × Node) := do
  let k := Frame.binders a.frames
  let q ← nodes.head?
  let q := peelBinders k q
  let mut rest := nodes.tail
  let term (n : Node) : Node := ((peelBinders (k + 1) n).getChildren[0]?).getD n
  let mut ps : Array Node := #[]
  for e in a.elems do
    match e with
    | .pattern ts =>
      let (here, more) := (rest.take ts.length, rest.drop ts.length)
      rest := more
      ps := ps.push (.app (.kind .INST_PATTERN) (here.map term).toArray)
    | .noPattern _ =>
      let some t := rest.head? | none
      rest := rest.tail
      ps := ps.push (.app (.kind .INST_NO_PATTERN) #[term t])
    | .qid n => ps := ps.push (.app (.kind .INST_ATTRIBUTE) #[strConst "qid", strConst n])
  let .app op cs := q | none
  return (q, .app op (cs.push (.app (.kind .INST_PATTERN_LIST) ps)))

/-- `n` with the quantifiers of `σ` annotated. -/
partial def annotate (σ : Std.HashMap Key Node) (n : Node) : Node :=
  if σ.isEmpty then n else
  match σ.get? ⟨n⟩ with
  | some m => m
  | none => match n with
    | .app op cs => .app op (cs.map (annotate σ))
    | n => n

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
  -- the sources of the terms Logos's parser reads (assertions, queries, the
  -- terms of `get-value`, the declared constants), in order
  let mut items : Array (ItemKind × String) := #[]
  -- the commands that produce output, with the items they read
  let mut cmds : Array (Command ⊕ (Bool × List Nat)) := #[]
  let mut produceModels := false
  let mut produceProofs := false
  let mut logic : Option String := none
  let mut decision : Option String := none
  let mut symbols : Array Symbol := #[]
  let mut checkSat := false
  -- the arithmetic types of the symbols (of the return types of functions)
  let mut numEnv : List (String × NumTy) := []
  let mut annots : Array Annot := #[]
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
    | .expr [.atom "set-option", .atom ":decision", .atom m] => decision := some m
    | .expr [.atom "set-option", .atom ":produce-models", .atom v] => produceModels := v == "true"
    | .expr [.atom "set-option", .atom ":produce-proofs", .atom v] => produceProofs := v == "true"
    | _ => pure ()
    match s with
    | .expr (.atom c :: _) =>
      if ignored.contains c then continue
      match s with
      | .expr [.atom "set-logic", .atom l] => logic := some l
      | .expr [.atom "check-sat"] =>
        checkSat := true
        cmds := cmds.push (.inl .checkSat)
      | .expr [.atom "get-model"] => cmds := cmds.push (.inl .getModel)
      | .expr [.atom "get-proof"] => cmds := cmds.push (.inl .getProof)
      | .expr [.atom "echo", .atom str] => cmds := cmds.push (.inl (.echo str))
      | .expr [.atom "get-info", .atom key] => cmds := cmds.push (.inl (.getInfo key))
      | .expr [.atom "get-value", .expr ts] =>
        let mut is := []
        for t in ts do
          let src := t.serialize
          let t := (cvc5Numerals numEnv cvc5Output false (bvNumerals t)).serialize
          eunoia := eunoia.push s!"(assume @s{items.size} (= {t} {t}))"
          is := is ++ [items.size]
          items := items.push (.value, src)
        cmds := cmds.push (.inr (false, is))
      | .expr [.atom "declare-const", .atom x, ty] =>
        if ty == .atom "Type" then sorts := sorts.push x else consts := consts.push x
        decls := decls.push s.serialize
        eunoia := eunoia.push s.serialize
        symbols := symbols.push ⟨[x], (Sexp.expr [.atom "declare-fun", .atom x, .expr [], ty]).serialize⟩
        if ty != .atom "Type" then
          eunoia := eunoia.push s!"(assume @s{items.size} (= {Eunoia.symbol x} {Eunoia.symbol x}))"
          items := items.push (.decl, x)
      | .expr [.atom "declare-fun", .atom x, .expr args, ret] =>
        consts := consts.push x
        -- Eunoia has no `declare-fun`; a function is a constant of arrow type.
        let ty := if args.isEmpty then ret else .expr (.atom "->" :: args ++ [ret])
        decls := decls.push (Sexp.expr [.atom "declare-const", .atom x, ty]).serialize
        eunoia := eunoia.push s.serialize
        symbols := symbols.push ⟨[x], s.serialize⟩
        eunoia := eunoia.push s!"(assume @s{items.size} (= {Eunoia.symbol x} {Eunoia.symbol x}))"
        items := items.push (.decl, x)
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
        let (t, as) ← stripAnnots [] t
        annots := annots ++ as.map ({ · with item := items.size })
        let t := t.serialize
        cmds := cmds.push (.inr (true, [items.size]))
        eunoia := eunoia.push s!"(assume @s{items.size} (= {t} {t}))"
        items := items.push (.simplify, t)
      | .expr [.atom "assert", t] =>
        if checkSat then throw "incremental scripts are not supported: an assertion after check-sat"
        let (t, as) ← stripAnnots [] t
        annots := annots ++ as.map ({ · with item := items.size })
        let t := t.serialize
        eunoia := eunoia.push s!"(assume @s{items.size} {t})"
        items := items.push (.assert, t)
      | .expr (.atom c :: _) =>
        -- commands that only produce output are reported when run
        if ["get-assertions", "get-assignment", "get-unsat-core", "get-unsat-assumptions",
            "get-option", "check-sat-assuming", "get-difficulty", "get-learned-literals",
            "get-timeout-core", "get-abduct", "get-interpolant", "get-qe", "block-model",
            "get-instantiations"].contains c then
          cmds := cmds.push (.inl (.unsupported s.serialize))
        else throw s!"unsupported command: {s.serialize}"
      | _ => throw s!"unsupported command: {s.serialize}"
    | _ => throw s!"unsupported command: {s.serialize}"
  -- the annotations, read after the assertions
  for a in annots do
    for r in a.reads do
      eunoia := eunoia.push s!"(assume @a{eunoia.size} {r.serialize})"
  let (assums, _) ← parseProof ("\n".intercalate eunoia.toList)
  let constName := fun i => consts[i - 1]?
  let dtNames := { mkDtNames dts with sort := fun i => sorts[i - 1]? }
  let names : Eunoia.Names :=
    { sort := fun i => sorts[i - 1]?, dt := dtNames }
  let read := items.toList.zip assums
  -- the annotated quantifiers
  let mut aux := assums.drop items.size
  -- (by command: the same quantifier may have other annotations elsewhere)
  let mut σs : Std.HashMap Nat (Std.HashMap Key Node) := {}
  for a in annots do
    let k := a.reads.length
    let nodes := (aux.take k).filterMap fun t => Node.ofEo [] (nameConsts constName t)
    aux := aux.drop k
    if nodes.length == k then
      if let some (q, q') := a.build nodes then
        σs := σs.insert a.item (((σs.get? a.item).getD {}).insert ⟨q⟩ q')
  let read := read.zipIdx
  let queryOf (i : Nat) (src : String) (t : Term) : Query :=
    ⟨src, (toNode constName t).map (annotate ((σs.get? i).getD {}))⟩
  let queries := read.filterMap fun (((k, src), t), i) =>
    if k == .simplify then some (queryOf i src t) else none
  let assertions := read.filterMap fun (((k, src), t), i) =>
    if k != .assert then none
    else some ⟨src, match Node.ofEo [] (nameConsts constName t) with
      | some n => .ok (annotate ((σs.get? i).getD {}) n)
      | none => .error "the term uses an operator telos does not support yet"⟩
  let declared := read.filterMap fun (((k, src), t), _) =>
    if k != .decl then none else
    match toNode constName t with
    | .ok n => some (src, n)
    | .error _ => none
  -- the instances of parametric datatypes, as the declarations write them
  let declTypes : Std.HashMap String Sexp := ss.foldl (init := {}) fun m s => match s with
    | .expr [.atom "declare-const", .atom x, ty] => m.insert x ty
    | .expr [.atom "declare-fun", .atom x, .expr args, ret] =>
      m.insert x (if args.isEmpty then ret else .expr (.atom "->" :: args ++ [ret]))
    | _ => m
  let rec instTypes (T : TypeNode) (ty : Sexp) (acc : List (String × String)) : List (String × String) :=
    match T, ty with
    | .function a r, .expr (.atom "->" :: a' :: rest) =>
      let r' := match rest with
        | [r'] => r'
        | rs => .expr (.atom "->" :: rs)
      instTypes r r' (instTypes a a' acc)
    | .datatype s _, ty => if (parInstanceOf s).isSome then (s, ty.serialize) :: acc else acc
    | _, _ => acc
  termination_by sizeOf T
  let parTypes : List (String × String) := declared.foldl (init := []) fun acc (x, n) =>
    match n.getType, declTypes.get? x with
    | some T, some ty => instTypes T ty acc
    | _, _ => acc
  let dtNames := { dtNames with parType := fun s => (parTypes.find? (·.1 == s)).map (·.2) }
  let names : Eunoia.Names := { names with dt := dtNames }
  let byItem : Std.HashMap Nat Query := read.foldl (init := {}) fun m (((k, src), t), i) =>
    if k == .simplify || k == .value then m.insert i (queryOf i src t) else m
  let commands := cmds.toList.map fun
    | .inl c => c
    | .inr (true, is) => .simplify (byItem.get? (is.headD 0) |>.getD ⟨"", .error "internal error: a lost query"⟩)
    | .inr (false, is) => .getValue (is.map fun i => (byItem.get? i).getD ⟨"", .error "internal error: a lost term"⟩)
  return { decls := decls.toList, names, queries, dtNames, assertions, logic, decision,
           symbols := symbols.toList, declared, commands, produceModels, produceProofs }

end Telos.Frontend
