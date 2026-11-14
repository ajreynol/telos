import Cpc.Parser
import Telos.Node.OfEo

/-!
# Printing Logos terms in Eunoia syntax

`Eunoia.print` writes a `Term` so that Logos's parser (and Ethos) reads it back
as the same term. Operator names come from the parser's own operator table
(`Eo.parserConfig.ops`), read in the other direction, so they stay in sync with
the signature.

The printer is not trusted: a printed proof is re-checked by whoever reads it,
and telos's tests check that Logos accepts the proofs it prints
(`TelosTests/Proof.lean`).
-/

open Eo

namespace Telos.Eunoia

/-- What the printer needs to know about an operator of the signature. -/
structure OpInfo where
  name : String
  indexArity : Nat
  /-- For a `:right-assoc-nil` operator, its nil terminator (given the first
  element). -/
  nil : Option (Option Term → Term)
  /-- Whether the operator binds variables, like `forall`. -/
  isBinder : Bool
  /-- For an operator applied to a list built from its arguments, like
  `distinct`, how the parser builds that list. -/
  argList : Option (List Term → Term) := none

/-- The placeholder index used to look up an indexed operator. -/
def dummyIndex : Term := .Numeral 0

/-- The table key of an operator head: its indices replaced by `dummyIndex`. -/
def headKey : Term → Term
  | .UOp1 op _ => .UOp1 op dummyIndex
  | .UOp2 op _ _ => .UOp2 op dummyIndex dummyIndex
  | .UOp3 op _ _ _ => .UOp3 op dummyIndex dummyIndex dummyIndex
  | t => t

/-- The indices of an indexed operator head. -/
def headIndices : Term → List Term
  | .UOp1 _ i => [i]
  | .UOp2 _ i j => [i, j]
  | .UOp3 _ i j k => [i, j, k]
  | _ => []

/-- The signature's operators, by head term. The first declaration of a head
wins. -/
def opTable : Std.TreeMap Term OpInfo termCmp :=
  parserConfig.ops.foldl (init := {}) fun m d =>
    match d.build (List.replicate d.indexArity dummyIndex) with
    | some h =>
      if m.contains (headKey h) then m
      else
        let nil := match d.arity with
          | .rightAssocNil nil => some nil
          | _ => none
        let argList := match d.arity with
          | .argList mk => some mk
          | _ => none
        m.insert (headKey h) { name := d.name, indexArity := d.indexArity, nil,
                               isBinder := d.binder.isSome, argList }
    | none => m

/-- Names for the uninterpreted sorts and constants of a problem, which Logos
numbers. -/
structure Names where
  sort : Nat → Option String := fun _ => none
  const : Nat → Option String := fun _ => none
  /-- Whether a variable of this name is a declared constant. telos represents
  declared constants as variables (`Node.var`); other variables are bound, and
  are printed as `(@var "x" T)` outside their binder (the signature's
  `(define @var ((s String) (T Type)) (eo::var s T))`). -/
  isConst : String → Bool := fun _ => false

def isSimpleSymbolChar (c : Char) : Bool :=
  c.isAlphanum || "~!@$%^&*_-+=<>.?/".contains c

/-- A symbol, quoted with `|…|` unless it is a simple symbol. -/
def symbol (s : String) : String :=
  if !s.isEmpty && s.all isSimpleSymbolChar && !(s.front.isDigit) then s
  else "|" ++ s ++ "|"

/-- An SMT-LIB string literal for a list of code points. -/
def stringLit (cs : List Nat) : String :=
  "\"" ++ String.join (cs.map fun c =>
    if c == 34 then "\"\""
    else if 32 ≤ c ∧ c ≤ 126 then (Char.ofNat c).toString
    else "\\u{" ++ String.ofList (Nat.toDigits 16 c) ++ "}") ++ "\""

/-- `#b…`: a bit-vector literal of the given width. -/
def binaryLit (w v : Int) : String :=
  let w := w.toNat
  let v := v.toNat
  "#b" ++ String.ofList ((List.range w).reverse.map fun i => if v.testBit i then '1' else '0')

/-- The elements and tail of `(op x₁ (op x₂ … (op xₙ tail)))`. -/
def rightAssocElems (h : Term) : Term → List Term × Term
  | .Apply (.Apply h' x) rest =>
    if h' == h then let (xs, t) := rightAssocElems h rest; (x :: xs, t) else ([], .Apply (.Apply h' x) rest)
  | t => ([], t)

/-- Print a term in Eunoia syntax. `bound` are the variables of the enclosing
binders. -/
partial def printIn (N : Names) (bound : List Term) (t : Term) : String :=
  let print := fun (_ : Names) => printIn N bound
  match t with
  | .Boolean b => if b then "true" else "false"
  | .Numeral n => toString n
  | .Rational q => s!"{q.num}/{q.den}"
  | .String s => stringLit s
  | .Binary w v => binaryLit w v
  | .Var (.String s) T =>
    let x := nativeStringToString s
    if bound.contains t || N.isConst x then symbol x
    else s!"(@var {stringLit s} {print N T})"
  | .Bool => "Bool"
  | .Type => "Type"
  | .FunType => "->"
  | .__eo_List => "@List"
  | .__eo_List_nil => "@list.nil"
  | .__eo_List_cons => "@list"
  | .USort i => symbol ((N.sort i).getD s!"@sort{i}")
  | .UConst i _ => symbol ((N.const i).getD s!"@const{i}")
  | .Apply .. =>
    let (h, xs) := eoSpine t
    match opTable.get? (headKey h) with
    | some info =>
      if info.isBinder then
        match xs with
        | [vs, body] =>
          match eoListElems vs with
          | some bvs =>
            let decls := bvs.map fun v => match v with
              | .Var (.String s) T => s!"({symbol (nativeStringToString s)} {print N T})"
              | v => s!"({print N v} ?)"
            s!"({info.name} ({" ".intercalate decls}) {printIn N (bvs ++ bound) body})"
          | none => curried h xs
        | _ => curried h xs
      else if let some mk := info.argList then
        -- `(distinct (@tlist x₁ … xₙ))` is written `(distinct x₁ … xₙ)`.
        match xs with
        | [l@(.Apply (.Apply lh _) _)] =>
          let (elems, _) := rightAssocElems lh l
          if mk elems == l then app (headName info h) elems else curried h xs
        | _ => curried h xs
      else
        match info.nil with
        | some nil =>
          let (elems, tail) := rightAssocElems h t
          match elems with
          | x :: _ =>
            if tail == nil (some x) then app (headName info h) elems
            else curried h xs
          | [] => curried h xs
        | none => app (headName info h) xs
    | none =>
      match h with
      | .Var .. | .UConst .. => app (print N h) xs
      | _ => curried h xs
  | _ =>
    match opTable.get? (headKey t) with
    | some info => headName info t
    | none => s!"<unprintable>"
where
  print (_ : Names) (t : Term) : String := printIn N bound t
  headName (info : OpInfo) (h : Term) : String :=
    if info.indexArity == 0 then info.name
    else s!"(_ {info.name} {" ".intercalate ((headIndices h).map (print N))})"
  app (f : String) (xs : List Term) : String :=
    s!"({f} {" ".intercalate (xs.map (print N))})"
  /-- Explicit curried application, `(_ f x)`, for spines that are not a plain
  application of an operator. -/
  curried (h : Term) (xs : List Term) : String :=
    xs.foldl (fun acc x => s!"(_ {acc} {print N x})") (print N h)

/-- Print a closed term in Eunoia syntax. -/
def print (N : Names) (t : Term) : String := printIn N [] t

end Telos.Eunoia
