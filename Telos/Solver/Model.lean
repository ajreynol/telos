import Std.Data.HashMap
import Std.Data.HashSet
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Core.Node.ToEo
import Telos.Solver.EqualityEngine
import Telos.Solver.Regex

/-!
# Models and their evaluation

A `sat` answer is certified by a model: a value for each free constant of the
input (a substitution), under which every input assertion evaluates to `true`
(`Model.satisfies`). The evaluation is telos's own (`Model.ev`), on nodes,
memoized, so that it is linear in the size of the input as a DAG.

Its theorem (`verification/TelosProofs/Solver/Model.lean`) relates it to
Logos's model semantics. The model of the substitution (`toSmtModel`) is well
formed, and evaluates each node as `Model.ev` does. So a model that satisfies
the input assertions makes them satisfiable. To make that correspondence
direct:
- the constants are keyed as Logos keys them: by the name of their Logos symbol
  (`keyName`), with their Logos type;
- function values carry their Logos types;
- the values of bound variables are a stack (`Env`), as Logos pushes them
  (`native_model_push`), so the model of the stack (`toSmtModelE`) is Logos's.

A quantifier is evaluated when a witness settles it (`quant`): an `exists` is
true, or a `forall` false, if its body evaluates to `true`, or `false`, for
some values of its variables among those of the model (`candidates`). A
`forall` that is true is not evaluated (the domains may be infinite).

The values are those of the theories telos solves: Booleans, the elements of
uninterpreted sorts (numbered), functions, datatype values, numbers, sets,
strings and regular expressions (`TRe`, membership by derivatives as Logos's).
A function is
given by a finite table (`FunTable`) with a default, curried as in Logos: a
function of two arguments maps the first to a function of one. A datatype
value is shaped as Logos's: a constructor (`dtc`) applied to its arguments
one at a time (`app`). Constructors, testers and selectors evaluate as in
Logos; a selector applied to the wrong constructor applies the model's
function for those applications, which Logos names
`@wrong_apply_sel_i_j` (`wrongSelName`), kept with the model's other symbols
(`Model.others`).

`buildModel` builds a model from the equality engine's classes of the relevant
terms, the subterms of the asserted literals, as cvc5's model builder does
(`TheoryEngineModelBuilder`, from its model equality engine, and
`TheoryDatatypes::collectModelInfo`):
- each class of an uninterpreted sort is an element of its own;
- each class of a datatype with a constructor term is that constructor applied
  to its arguments' values; one without (which the theory did not need to
  split) gets a value of its own, distinct from the others', with a
  constructor its testers do not exclude (`classValues`);
- each relevant application gives an entry of its function's table, and each
  relevant selector applied to the wrong constructor an entry of the function
  of its wrong applications (every selector of the input has one);
- the constants not otherwise given a value get a default, then the
  definitions of the variables solved by preprocessing are evaluated (in
  passes, as one may use another).

The builder is not trusted: `satisfies` checks its result.
-/

open Eo Smtm SmtEval

namespace Telos.Solver

/-- The Logos type of a type. -/
def tyS (T : TypeNode) : SmtType := __eo_to_smt_type T.toEo

/-- The name of the Logos symbol of the constant `x` (`native_uconst_id`). -/
def keyName (x : String) : native_String := native_uconst_id (constId x)

/-- A value of a model. -/
inductive MVal where
  | bool (b : Bool)
  /-- The `i`-th element of the uninterpreted sort `s` (Logos's `UValue`). -/
  | uval (s : Nat) (i : Nat)
  /-- The function of the table `fid` (`FunTable`), of Logos type `dom → rng`. -/
  | fn (fid : Nat) (dom rng : SmtType)
  /-- Constructor `i` of the datatype `s` of the block `dd` (Logos's
  `DtCons`). -/
  | dtc (s : native_String) (dd : SmtDatatypeDecl) (i : Nat)
  /-- A value applied to another: a constructor to its arguments, one at a
  time (Logos's `Apply`). -/
  | app (f a : MVal)
  /-- An integer (Logos's `Numeral`). -/
  | int (i : Int)
  /-- A real, rational (Logos's `Real` of a rational). -/
  | rat (q : Rat)
  /-- The empty set of elements of Logos type `T` (Logos's `Set` of the map
  with default `false`). -/
  | sempty (T : SmtType)
  /-- The set `s` with the element `e` (Logos's map `s` updated at `e` to
  `true`). A set is compared with another by its elements, as Logos compares
  them (`MVal.veq`), not structurally. -/
  | sins (e s : MVal)
  /-- A string, of code points (Logos's `Seq` of `Char`s). -/
  | str (w : List Nat)
  /-- A regular expression (Logos's `RegLan`). Two are compared structurally
  (`TRe.ceq`), as Logos's values are, but `=` on them is not evaluated: Logos's
  is the equality of their languages. -/
  | re (r : TRe)
  deriving DecidableEq, Inhabited

/-- A character as Logos has it: one that is not valid (`native_char_valid`)
is `0`. The model's strings are of valid characters; the clamp makes every
`str` a well-typed Logos string. -/
def MVal.clampChar (c : Nat) : Nat := if c < 196608 then c else 0

/-- The Logos type of constructor `i` of the datatype `s` of `dd`. -/
def consType (s : native_String) (dd : SmtDatatypeDecl) (i : Nat) : SmtType :=
  __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd) (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i

/-- Whether a value is a set. -/
def MVal.isSet : MVal → Bool
  | .sempty _ | .sins .. => true
  | _ => false

/-- The Logos type of a value; a set whose elements are not all of its element
type has none. -/
def MVal.ty : MVal → SmtType
  | .bool _ => .Bool
  | .uval s _ => .USort s
  | .fn _ d r => .FunType d r
  | .dtc s dd i => consType s dd i
  | .app f a => __smtx_typeof_apply_value f.ty a.ty
  | .int _ => .Int
  | .rat _ => .Real
  | .str _ => .Seq .Char
  | .re _ => .RegLan
  | .sempty T => .Set T
  | .sins e s =>
    if s.isSet then
      match s.ty with
      | .Set T => if e.ty == T then .Set T else .None
      | _ => .None
    else .None

/-- The elements of a set (of `sins`), in order of insertion, last first. -/
def MVal.elems : MVal → List MVal
  | .sins e s => e :: s.elems
  | _ => []

theorem MVal.sizeOf_lt_of_mem_elems : ∀ {s e : MVal}, e ∈ s.elems → sizeOf e < sizeOf s
  | .sins a s, e, h => by
    simp only [MVal.elems, List.mem_cons] at h
    rcases h with rfl | h
    · simp; omega
    · have := MVal.sizeOf_lt_of_mem_elems h; simp; omega
  | .sempty _, _, h | .bool _, _, h | .uval .., _, h | .fn .., _, h | .dtc .., _, h | .app .., _, h
  | .int _, _, h | .rat _, _, h | .str _, _, h | .re _, _, h => by simp [MVal.elems] at h

/-- **Equality of values, as Logos's** (`native_veq` of their Logos values):
two well-typed sets are equal when they have the same element type and the
same elements, two ill-typed ones are both `NotValue`; the others are
compared structurally. -/
def MVal.veq (a b : MVal) : Bool :=
  if a.isSet || b.isSet then
    if !(a.isSet && b.isSet) then false else
    let wa := a.ty != .None
    let wb := b.ty != .None
    if wa && wb then
      a.ty == b.ty &&
        a.elems.attach.all (fun ⟨e, _⟩ => b.elems.attach.any fun ⟨f, _⟩ => MVal.veq e f) &&
        b.elems.attach.all (fun ⟨f, _⟩ => a.elems.attach.any fun ⟨e, _⟩ => MVal.veq f e)
    else !wa && !wb
  else match a, b with
    | .app f x, .app g y => MVal.veq f g && MVal.veq x y
    | .str x, .str y => x.map MVal.clampChar == y.map MVal.clampChar
    | .re x, .re y => x.ceq y
    | a, b => a == b
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := MVal.sizeOf_lt_of_mem_elems ‹_ ∈ a.elems›; have := MVal.sizeOf_lt_of_mem_elems ‹_ ∈ b.elems›; omega)
    | omega

/-- Whether a value is a regular expression. -/
def MVal.isRe : MVal → Bool
  | .re _ => true
  | _ => false

/-- An ill-typed set, whose Logos value is `NotValue`: no function or
constructor applies to it (Logos's application of anything to `NotValue` is
`NotValue`). -/
def MVal.notValue (v : MVal) : Bool := v.isSet && v.ty == .None

/-- The set with the elements `es` added to `s`. -/
def MVal.insAll (s : MVal) (es : List MVal) : MVal := es.foldr .sins s

/-- Constructor `i` of `s` applied to `args`. -/
def MVal.mkDt (s : native_String) (dd : SmtDatatypeDecl) (i : Nat) (args : List MVal) : MVal :=
  args.foldl .app (.dtc s dd i)

/-- The head of an application (`__smtx_apply_head_value`). -/
def MVal.head : MVal → MVal
  | .app f _ => f.head
  | v => v

/-- The argument at position `n` of an application of `npos` arguments
(`__smtx_apply_arg_nth_value`). -/
def MVal.argNth : MVal → Nat → Nat → Option MVal
  | .app f a, n, npos + 1 => if n == npos then some a else f.argNth n npos
  | _, _, _ => none

structure FunTable where
  dom : SmtType
  rng : SmtType
  entries : List (MVal × MVal)
  default : MVal
  deriving Inhabited

structure Model where
  /-- The constants, by the name of their Logos symbol: their Logos type and
  their value. -/
  consts : Std.HashMap native_String (SmtType × MVal) := {}
  funs : Array FunTable := #[]
  /-- Other symbols of the model, by name and type: the functions that give
  the values of selectors applied to the wrong constructor
  (`native_wrong_apply_sel_id`). -/
  others : Array (native_String × SmtType × MVal) := #[]
  deriving Inhabited

namespace Model

/-- The value of the symbol named `x` of Logos type `T`: among the other
symbols, then the constants (as `toSmtModel` looks it up). -/
def lookup (M : Model) (x : native_String) (T : SmtType) : Option MVal :=
  match (M.others.find? fun (y, U, _) => y == x && U == T) with
  | some (_, _, v) => some v
  | none =>
    match M.consts.get? x with
    | some (T', v) => if T' == T then some v else none
    | none => none

/-- The value of the constant `x` of type `T`. -/
def const (M : Model) (x : String) (T : TypeNode) : Option MVal := M.lookup (keyName x) (tyS T)

/-- The datatype constructor of a node's Logos term. -/
def consOf? (f : Node) : Option (native_String × SmtDatatypeDecl × Nat) :=
  match f.toSmt with
  | .DtCons s dd i => some (s, dd, i)
  | _ => none

/-- The datatype selector of a node's Logos term. -/
def selOf? (f : Node) : Option (native_String × SmtDatatypeDecl × Nat × Nat) :=
  match f.toSmt with
  | .DtSel s dd i j => some (s, dd, i, j)
  | _ => none

/-- The name of the function of the wrong applications of selector `j` of
constructor `i` (Logos's `native_wrong_apply_sel_id`, which lives with Logos's
model semantics, outside what telos imports; the two are the same,
`wrongSelName_eq`). -/
def wrongSelName (n m : Nat) : native_String :=
  (native_string_lit "@wrong_apply_sel_") ++ (native_string_lit (toString n)) ++ (native_string_lit "_") ++
    (native_string_lit (toString m))

/-- The Logos type of the function of the wrong applications of selector `j`
of constructor `i` of `s`. -/
def wrongSelType (s : native_String) (dd : SmtDatatypeDecl) (i j : Nat) : SmtType :=
  .FunType (.Datatype s dd) (__smtx_ret_typeof_sel s dd i j)

/-- Apply a function value to an argument. -/
def apply (M : Model) (f a : MVal) : Option MVal :=
  if a.notValue then none else
  match f with
  | .fn fid dom rng =>
    match M.funs[fid]? with
    | some t =>
      if t.dom == dom && t.rng == rng then
        match t.entries.find? (·.1.veq a) with
        | some (_, v) => some v
        | none => some t.default
      else none
    | none => none
  | _ => none


/-- The names of Logos's functions of division by zero
(`native_div_by_zero_id`, `native_mod_by_zero_id`, `native_qdiv_by_zero_id`;
equal, `divByZeroName_eq`). -/
def divByZeroName : native_String := native_string_lit "@div_by_zero"
def modByZeroName : native_String := native_string_lit "@mod_by_zero"
def qdivByZeroName : native_String := native_string_lit "@qdiv_by_zero"

/-- Integer division and modulus, total or not, and division by zero, as
Logos evaluates them: by a nonzero integer, `native_div_total` and
`native_mod_total`; by zero, the model's functions `@div_by_zero`,
`@mod_by_zero` and `@qdiv_by_zero` (the values of cvc5's
`@int_div_by_zero`, `@mod_by_zero` and `@div_by_zero` skolems) applied to the
dividend. `none` for the other operations (`combine`'s). -/
def divMod? (M : Model) (k : Kind) (vs : List MVal) : Option (Option MVal) :=
  match k, vs with
  | .INTS_DIVISION, [.int a, .int b] =>
    some (if b == 0 then (M.lookup divByZeroName (.FunType .Int .Int)).bind (M.apply · (.int a))
          else some (.int (native_div_total a b)))
  | .INTS_MODULUS, [.int a, .int b] =>
    some (if b == 0 then (M.lookup modByZeroName (.FunType .Int .Int)).bind (M.apply · (.int a))
          else some (.int (native_mod_total a b)))
  | .INTS_DIVISION_TOTAL, [.int a, .int b] => some (some (.int (native_div_total a b)))
  | .INTS_MODULUS_TOTAL, [.int a, .int b] => some (some (.int (native_mod_total a b)))
  | .DIVISION, [.rat a, .rat b] =>
    if b == 0 then some ((M.lookup qdivByZeroName (.FunType .Real .Real)).bind (M.apply · (.rat a)))
    else none
  | _, _ => none

/-- Apply a function value to arguments, left to right. -/
def applyAll (M : Model) (f : MVal) : List MVal → Option MVal
  | [] => some f
  | a :: as => match M.apply f a with
    | some g => M.applyAll g as
    | none => none

/-- The tables are well typed: their entries and their defaults have the
table's range. -/
def tablesOk (M : Model) : Bool :=
  M.funs.all fun t => t.entries.all (fun (_, v) => v.ty == t.rng) && t.default.ty == t.rng

/-- Each constant, and each other symbol, has a value of its type. -/
def constsOk (M : Model) : Bool :=
  (M.consts.toList.all fun (_, T, v) => v.ty == T) && M.others.all fun (_, T, v) => v.ty == T

/-- The memo of the evaluation: the value of each node evaluated, if any. -/
abbrev Memo := Std.HashMap Key (Option MVal)

/-- The Boolean values of a list of values. -/
def bools : List MVal → Option (List Bool)
  | [] => some []
  | .bool b :: vs => (bools vs).map (b :: ·)
  | _ => none

/-! ### Arithmetic, as Logos evaluates it (`__smtx_model_eval_plus`, ...): on two
integers or two reals, nothing otherwise -/

def plusV : MVal → MVal → Option MVal
  | .int a, .int b => some (.int (a + b))
  | .rat a, .rat b => some (.rat (a + b))
  | _, _ => none

def multV : MVal → MVal → Option MVal
  | .int a, .int b => some (.int (a * b))
  | .rat a, .rat b => some (.rat (a * b))
  | _, _ => none

def subV : MVal → MVal → Option MVal
  | .int a, .int b => some (.int (a + -b))
  | .rat a, .rat b => some (.rat (a + -b))
  | _, _ => none

/-- Division by a nonzero rational (Logos's `qdiv` then is `qdiv_total`; by
zero, its value is that of the model's `@div_by_zero` function: not
evaluated). -/
def divV : MVal → MVal → Option MVal
  | .rat a, .rat b => if b == 0 then none else some (.rat (a / b))
  | _, _ => none

def negV : MVal → Option MVal
  | .int a => some (.int (-a))
  | .rat a => some (.rat (-a))
  | _ => none

def ltV : MVal → MVal → Option MVal
  | .int a, .int b => some (.bool (decide (a < b)))
  | .rat a, .rat b => some (.bool (decide (a < b)))
  | _, _ => none

def leqV : MVal → MVal → Option MVal
  | .int a, .int b => some (.bool (decide (a ≤ b)))
  | .rat a, .rat b => some (.bool (decide (a ≤ b)))
  | _, _ => none

/-- The neutral element that ends an `n`-ary sum or product, of the type of its
first argument (the typed nil, `typedNilOfType`). -/
def chainNil : Kind → SmtType → Option MVal
  | .ADD, .Int => some (.int 0)
  | .ADD, .Real => some (.rat 0)
  | .MULT, .Int => some (.int 1)
  | .MULT, .Real => some (.rat 1)
  | .STRING_CONCAT, .Seq .Char => some (.str [])
  | _, _ => none

/-- `str.substr`, as Logos's `native_seq_extract`. -/
def strExtract (w : List Nat) (i n : Int) : List Nat :=
  let len : Int := Int.ofNat w.length
  if i < 0 || n <= 0 || i >= len then []
  else (w.drop (Int.toNat i)).take (Int.toNat (min n (len - i)))

/-- Logos's `impl_native_char_to_lower` and `impl_native_char_to_upper`. -/
def charToLower (c : Nat) : Nat := if 65 ≤ c && c ≤ 90 then c + 32 else c
def charToUpper (c : Nat) : Nat := if 97 ≤ c && c ≤ 122 then c - 32 else c

/-- `str.to_code` of a string: the code of its one character (clamped, as its
Logos value has it), else `-1`. -/
def strCode : List Nat → Int
  | [c] => Int.ofNat (MVal.clampChar c)
  | _ => -1

/-- The concatenation of two strings. -/
def concatV : MVal → MVal → Option MVal
  | .str a, .str b => some (.str (a ++ b))
  | _, _ => none

/-- The concatenation, union and intersection of two regular expressions. -/
def reConcatV : MVal → MVal → Option MVal
  | .re a, .re b => some (.re (TRe.mkConcat a b))
  | _, _ => none

def reUnionV : MVal → MVal → Option MVal
  | .re a, .re b => some (.re (TRe.mkUnion a b))
  | _, _ => none

def reInterV : MVal → MVal → Option MVal
  | .re a, .re b => some (.re (TRe.mkInter a b))
  | _, _ => none

/-- A right-associated chain of a binary operation, ending in `nil`. -/
def chainV (f : MVal → MVal → Option MVal) (nil : MVal) : List MVal → Option MVal
  | [] => some nil
  | v :: vs => (chainV f nil vs).bind (f v)

/-- Whether `k` is an operator of regular expressions, or membership in one
(`combineRe`). -/
def isReKind : Kind → Bool
  | .REGEXP_CONCAT | .REGEXP_UNION | .REGEXP_INTER | .STRING_TO_REGEXP | .STRING_IN_REGEXP
  | .REGEXP_NONE | .REGEXP_ALL | .REGEXP_ALLCHAR | .REGEXP_STAR | .REGEXP_PLUS | .REGEXP_OPT
  | .REGEXP_COMPLEMENT | .REGEXP_DIFF | .REGEXP_RANGE => true
  | _ => false

/-- The value of an operator of regular expressions, or of membership in one,
of kind `k` on the values `vs` of its children. -/
def combineRe (k : Kind) (vs : List MVal) : Option MVal :=
  match k, vs with
  | .REGEXP_CONCAT, vs => if 2 ≤ vs.length then chainV reConcatV (.re .epsilon) vs else none
  | .REGEXP_UNION, vs => if 2 ≤ vs.length then chainV reUnionV (.re .empty) vs else none
  | .REGEXP_INTER, vs => if 2 ≤ vs.length then chainV reInterV (.re (.star .allchar)) vs else none
  | .STRING_TO_REGEXP, [.str w] => some (.re (TRe.ofList w))
  | .STRING_IN_REGEXP, [.str w, .re r] => some (.bool (TRe.inRe w r))
  | .REGEXP_NONE, [] => some (.re .empty)
  | .REGEXP_ALL, [] => some (.re (.star .allchar))
  | .REGEXP_ALLCHAR, [] => some (.re .allchar)
  | .REGEXP_STAR, [.re r] => some (.re (TRe.mkStar r))
  | .REGEXP_PLUS, [.re r] => some (.re (TRe.mkConcat r (TRe.mkStar r)))
  | .REGEXP_OPT, [.re r] => some (.re (TRe.mkUnion r .epsilon))
  | .REGEXP_COMPLEMENT, [.re r] => some (.re (TRe.mkComp r))
  | .REGEXP_DIFF, [.re a, .re b] => some (.re (TRe.mkInter a (TRe.mkComp b)))
  | .REGEXP_RANGE, [.str a, .str b] => some (.re (TRe.mkRange a b))
  | _, _ => none

/-- Whether `k` is an operator of strings of `combineStr`. -/
def isStrFnKind : Kind → Bool
  | .STRING_CHARAT | .STRING_CONTAINS | .STRING_PREFIX | .STRING_SUFFIX | .STRING_LT | .STRING_LEQ
  | .STRING_INDEXOF | .STRING_REPLACE | .STRING_REPLACE_ALL | .STRING_UPDATE | .STRING_INDEXOF_RE
  | .STRING_REPLACE_RE | .STRING_REPLACE_RE_ALL | .STRING_FROM_CODE | .STRING_STOI | .STRING_ITOS => true
  | _ => false

/-- The order of strings (`native_str_lt`). -/
def strLt (w u : List Nat) : Bool := decide (w.map MVal.clampChar < u.map MVal.clampChar)

/-- `str.update` (`native_seq_update`). -/
def strUpdate (w : List Nat) (i : Int) (u : List Nat) : List Nat :=
  if i < 0 || Int.ofNat w.length <= i then w
  else w.take i.toNat ++ u.take (w.length - i.toNat) ++ w.drop (i.toNat + u.length)

/-- `str.to_int` (`native_str_to_int`). -/
def strToInt (w : List Nat) : Int :=
  match w with
  | [] => -1
  | _ => if w.all (fun c => 48 <= c && c <= 57) then
      Int.ofNat (w.foldl (fun acc c => 10 * acc + (c - 48)) 0) else -1

/-- A string of valid characters. -/
def validStr (w : List Nat) : Option MVal :=
  if w.all (fun c => decide (c < 196608)) then some (.str w) else none

/-- The value of an extended function of strings of kind `k` on the values `vs`
of its children, as Logos evaluates it: the searches by the regular expression
of the string searched for. -/
def combineStr (k : Kind) (vs : List MVal) : Option MVal :=
  match k, vs with
  | .STRING_CHARAT, [.str w, .int i] => some (.str (strExtract w i 1))
  | .STRING_CONTAINS, [.str w, .str u] => some (.bool (decide (0 ≤ TRe.indexOf w (TRe.ofList u) 0)))
  | .STRING_PREFIX, [.str u, .str w] => some (.bool ((MVal.str u).veq (.str (strExtract w 0 u.length))))
  | .STRING_SUFFIX, [.str u, .str w] =>
    some (.bool ((MVal.str u).veq (.str (strExtract w (w.length + -(u.length : Int)) u.length))))
  | .STRING_LT, [.str w, .str u] => some (.bool (strLt w u))
  | .STRING_LEQ, [.str w, .str u] => some (.bool ((MVal.str w).veq (.str u) || strLt w u))
  | .STRING_INDEXOF, [.str w, .str u, .int i] => some (.int (TRe.indexOf w (TRe.ofList u) i))
  | .STRING_INDEXOF_RE, [.str w, .re r, .int i] => some (.int (TRe.indexOf w r i))
  | .STRING_REPLACE, [.str w, .str u, .str z] => some (.str (TRe.replace w (TRe.ofList u) z))
  | .STRING_REPLACE_RE, [.str w, .re r, .str z] => some (.str (TRe.replace w r z))
  | .STRING_REPLACE_ALL, [.str w, .str u, .str z] => some (.str (TRe.replaceAll w (TRe.ofList u) z))
  | .STRING_REPLACE_RE_ALL, [.str w, .re r, .str z] => some (.str (TRe.replaceAll w r z))
  | .STRING_UPDATE, [.str w, .int i, .str u] => some (.str (strUpdate w i u))
  | .STRING_FROM_CODE, [.int i] => validStr (if 0 ≤ i && decide (i.toNat < 196608) then [i.toNat] else [])
  | .STRING_STOI, [.str w] => some (.int (strToInt (w.map MVal.clampChar)))
  | .STRING_ITOS, [.int i] => validStr (if i < 0 then [] else native_string_lit (toString i))
  | _, _ => none

/-- The value of a connective (or equality, or `ite`, or an arithmetic, string,
set or regular expression operation) of kind `k` on the values `vs` of its
children `cs`. -/
def combine (k : Kind) (cs : Array Node) (vs : List MVal) : Option MVal :=
  if isReKind k then combineRe k vs else
  if isStrFnKind k then combineStr k vs else
  match k, vs with
  | .NOT, [.bool b] => some (.bool !b)
  | .AND, vs => if 2 ≤ vs.length then (bools vs).map fun bs => .bool (bs.all id) else none
  | .OR, vs => if 2 ≤ vs.length then (bools vs).map fun bs => .bool (bs.any id) else none
  | .IMPLIES, [.bool a, .bool b] => some (.bool (!a || b))
  | .XOR, [.bool a, .bool b] => some (.bool (a != b))
  | .EQUAL, [a, b] => if a.isRe then none else some (.bool (a.veq b))
  | .ITE, [.bool c, a, b] => some (if c then a else b)
  | .ADD, vs => if 2 ≤ vs.length then
      (chainNil .ADD (cs[0]?.getD default).smtTypeF).bind fun nil => chainV plusV nil vs
    else none
  | .MULT, vs => if 2 ≤ vs.length then
      (chainNil .MULT (cs[0]?.getD default).smtTypeF).bind fun nil => chainV multV nil vs
    else none
  | .STRING_CONCAT, vs => if 2 ≤ vs.length then
      (chainNil .STRING_CONCAT (cs[0]?.getD default).smtTypeF).bind fun nil => chainV concatV nil vs
    else none
  | .SUB, [a, b] => subV a b
  | .DIVISION, [a, b] => divV a b
  | .NEG, [a] => negV a
  | .LT, [a, b] => ltV a b
  | .LEQ, [a, b] => leqV a b
  | .GT, [a, b] => ltV b a
  | .GEQ, [a, b] => leqV b a
  | .TO_REAL, [.int i] => some (.rat i)
  | .STRING_LENGTH, [.str w] => some (.int w.length)
  | .STRING_TO_CODE, [.str w] => some (.int (strCode w))
  | .STRING_IS_DIGIT, [.str w] => some (.bool (decide (48 ≤ strCode w) && decide (strCode w ≤ 57)))
  | .STRING_REV, [.str w] => some (.str w.reverse)
  | .STRING_SUBSTR, [.str w, .int i, .int n] => some (.str (strExtract w i n))
  | .STRING_TO_LOWER, [.str w] => some (.str ((w.map MVal.clampChar).map charToLower))
  | .STRING_TO_UPPER, [.str w] => some (.str ((w.map MVal.clampChar).map charToUpper))
  | .SET_SINGLETON, [x] => some (.sins x (.sempty x.ty))
  | .SET_UNION, [a, b] => setOp a b fun _ => some (b.insAll a.elems)
  | .SET_INTER, [a, b] => setOp a b fun T =>
    some ((MVal.sempty T).insAll (a.elems.filter fun e => b.elems.any (e.veq ·)))
  | .SET_MINUS, [a, b] => setOp a b fun T =>
    some ((MVal.sempty T).insAll (a.elems.filter fun e => !b.elems.any (e.veq ·)))
  | .SET_MEMBER, [x, s] =>
    match s.ty with
    | .Set _ => if s.isSet then some (.bool (s.elems.any (x.veq ·))) else none
    | _ => none
  -- `(divisible k t)`: `(= (mod_total t k) 0)`, as Logos evaluates it
  | .DIVISIBLE, [.int k, .int t] => some (.bool (native_mod_total t k == 0))
  | _, _ => none
where
  /-- An operation on two well-typed sets of one type `T`. -/
  setOp (a b : MVal) (f : SmtType → Option MVal) : Option MVal :=
    match a.ty, b.ty with
    | .Set T, .Set U => if a.isSet && b.isSet && T == U then f T else none
    | _, _ => none

/-- The value of an indexed operator of kind `k`, of indices `is`, on the
values `vs` of its children. -/
def combineIdx (k : Kind) (is : List Int) (vs : List MVal) : Option MVal :=
  match k, is, vs with
  | .REGEXP_REPEAT, [i], [.re r] => some (.re (r.exp i.toNat))
  | .REGEXP_LOOP, [i, j], [.re r] => some (.re (TRe.loop i j r))
  | _, _, _ => none

/-- The CPC list of the arguments of a `distinct` (as `Node.toEo` writes it). -/
def distinctList (cs : Array Node) : Term :=
  let xs := cs.toList.map Node.toEo
  eoRightAssocNil UserOp._at__at_TypedList_cons
    (typedNil UserOp._at__at_TypedList_cons (xs.headD Term.Stuck)) xs

/-- The arguments of a `distinct` have one type, as its Logos translation
requires (else it is not a Logos term). -/
def distinctTyped (cs : Array Node) : Bool :=
  __eo_to_smt_typed_list_elem_type (distinctList cs) != SmtType.None

/-- The values are pairwise distinct. -/
def distinctVals : List MVal → Bool
  | [] => true
  | v :: vs => vs.all (fun w => !(v.veq w)) && distinctVals vs

/-- The values of the bound variables in scope: name, Logos type and value,
the innermost first (as Logos's `native_model_push` stacks them). -/
abbrev Env := List (native_String × SmtType × MVal)

/-- The value of the bound variable `x` of Logos type `T`: the innermost. -/
def Env.lookup : Env → native_String → SmtType → Option MVal
  | [], _, _ => none
  | (y, U, v) :: env, x, T => if y == x && U == T then some v else Env.lookup env x T

/-- The list without the values equal (`veq`) to a later one. -/
def dedupVals : List MVal → List MVal
  | [] => []
  | v :: vs => let r := dedupVals vs; if r.any (v.veq ·) then r else v :: r

/-- The witnesses tried for a bound variable of Logos type `T`: the values of
that type in the model (of its constants, in its tables, and the Booleans),
and small defaults of the arithmetic types and strings. -/
def candidates (M : Model) (T : SmtType) : List MVal :=
  let vs := [MVal.bool true, .bool false, .int 0, .int 1, .int (-1), .rat 0, .rat 1, .str []] ++
    M.consts.toList.map (·.2.2) ++
    M.funs.toList.flatMap fun t => t.default :: t.entries.flatMap fun (a, b) => [a, b]
  dedupVals (vs.filter (·.ty == T))

mutual
  /-- Evaluate a node, memoized (the memo is threaded, so it is updated in
  place); `none` outside the fragment evaluated (Booleans, equalities, `ite`,
  declared constants and their applications) or when the fuel runs out. -/
  def ev (M : Model) (env : Env) : Nat → Node → Memo → Option MVal × Memo
    | 0, _, S => (none, S)
    | n + 1, t, S =>
      match S.get? ⟨t⟩ with
      | some v => (v, S)
      | none =>
        match evNode M env n t S with
        | (v, S) => (v, S.insert ⟨t⟩ v)
  termination_by n => (n, 0, 0)

  /-- Evaluate a node from its children. -/
  def evNode (M : Model) (env : Env) (n : Nat) (t : Node) (S : Memo) : Option MVal × Memo :=
    match t with
    | .const (.boolean b) => (some (.bool b), S)
    | .const (.integer i) => (some (.int i), S)
    | .const (.rational q) => (some (.rat q), S)
    | .const (.string w) => (if w.all (fun c => decide (c < 196608)) then some (.str w) else none, S)
    | .const (.emptySet T) => (if tyS T == .None then none else some (.sempty (tyS T)), S)
    | .var x T => (M.const x T, S)
    | .boundVar x T => (env.lookup (native_string_lit x) (tyS T), S)
    | .app (.kind .DISTINCT) cs =>
      if distinctTyped cs then
        match evList M env n cs.toList S with
        | (none, S) => (none, S)
        | (some vs, S) => (if 2 ≤ vs.length && !vs.any (·.isRe) then some (.bool (distinctVals vs)) else none, S)
      else (none, S)
    | .app (.kind k) cs =>
      if k == .FORALL || k == .EXISTS then (quant M env n (k == .EXISTS) cs, S) else
      match evList M env n cs.toList S with
      | (none, S) => (none, S)
      | (some vs, S) => ((M.divMod? k vs).getD (combine k cs vs), S)
    | .app (.indexed k is) cs =>
      match evList M env n cs.toList S with
      | (none, S) => (none, S)
      | (some vs, S) => (combineIdx k is.toList vs, S)
    | .app (.node .APPLY_UF (.var f T)) cs =>
      match M.const f T with
      | none => (none, S)
      | some fv =>
        match evList M env n cs.toList S with
        | (none, S) => (none, S)
        | (some vs, S) => (if vs.isEmpty then none else M.applyAll fv vs, S)
    | .app (.node .APPLY_CONSTRUCTOR f@(.const (.dtCons ..))) cs =>
      match consOf? f with
      | none => (none, S)
      | some (s, dd, i) =>
        match evList M env n cs.toList S with
        | (none, S) => (none, S)
        | (some vs, S) => (if vs.any (·.notValue) then none else some (MVal.mkDt s dd i vs), S)
    | .app (.node .APPLY_TESTER f@(.const (.dtCons ..))) cs =>
      match consOf? f, cs.toList with
      | some (s, dd, i), [x] =>
        match ev M env n x S with
        | (none, S) => (none, S)
        | (some v, S) => (some (.bool (v.head == .dtc s dd i)), S)
      | _, _ => (none, S)
    | .app (.node .APPLY_SELECTOR f@(.const (.dtSel ..))) cs =>
      match selOf? f, cs.toList with
      | some (s, dd, i, j), [x] =>
        match ev M env n x S with
        | (none, S) => (none, S)
        | (some v, S) =>
          (if v.head == .dtc s dd i then v.argNth j (__smtx_dt_num_sels (__smtx_dd_lookup s dd) i)
           else (M.lookup (wrongSelName i j) (wrongSelType s dd i j)).bind (M.apply · v), S)
      | _, _ => (none, S)
    | .const (.dtCons ..) => (consOf? t |>.map fun (s, dd, i) => .dtc s dd i, S)
    | _ => (none, S)
  termination_by (n, 3, 0)

  /-- A quantifier, an `exists` (`pol`) or a `forall`, of the children `cs`, by
  a witness among the candidates (`candidates`): an `exists` is true if its
  body is true for one, a `forall` false if its body is false for one; else it
  is not evaluated. -/
  def quant (M : Model) (env : Env) (n : Nat) (pol : Bool) (cs : Array Node) : Option MVal :=
    match cs.toList with
    | [.app (.kind .BOUND_VAR_LIST) vs, body] =>
      if !vs.isEmpty && (witness M env n pol body vs.toList).isSome then some (.bool pol) else none
    | _ => none
  termination_by (n, 2, 0)

  /-- Values of the bound variables `vs` (pushed on `env`) for which `body`
  evaluates to `pol` (with a memo of its own, as its value depends on them). -/
  def witness (M : Model) (env : Env) (n : Nat) (pol : Bool) (body : Node) :
      List Node → Option Env
    | [] => match (ev M env n body {}).1 with
      | some (.bool b) => if b == pol then some env else none
      | _ => none
    | .boundVar x T :: rest =>
      (candidates M (tyS T)).findSome? fun v =>
        witness M ((native_string_lit x, tyS T, v) :: env) n pol body rest
    | _ :: _ => none
  termination_by l => (n, 1, l.length)

  /-- Evaluate a list of nodes. -/
  def evList (M : Model) (env : Env) (n : Nat) : List Node → Memo → Option (List MVal) × Memo
    | [], S => (some [], S)
    | c :: cs, S =>
      match ev M env n c S with
      | (none, S) => (none, S)
      | (some v, S) =>
        match evList M env n cs S with
        | (none, S) => (none, S)
        | (some vs, S) => (some (v :: vs), S)
  termination_by l => (n, 1, l.length)
end

/-- The fuel of the evaluation: a bound on the depth of the nodes. -/
def fuel : Nat := 1 <<< 20

/-- **The model satisfies the assertions**: its tables and constants are well
typed, and every assertion evaluates to `true`. -/
def satisfies (M : Model) (as : List Node) : Bool :=
  M.tablesOk && M.constsOk &&
    (match M.evList [] fuel as {} with
     | (some vs, _) => vs.all (· == .bool true)
     | (none, _) => false)

/-- Evaluate one node. -/
def eval (M : Model) (t : Node) : Option MVal := (M.ev [] fuel t {}).1

end Model

/-! ## Building a model -/

/-! ### Values of datatypes -/

/-- The constructors of a datatype, as the lists of their field types. -/
def dtConses : SmtDatatype → List (List SmtType)
  | .sum c d => fields c :: dtConses d
  | .null => []
where
  fields : SmtDatatypeCons → List SmtType
    | .cons T c => T :: fields c
    | .unit => []

/-- The constructors of the datatype `s` of `dd`, their field types resolved. -/
def consesOf (s : native_String) (dd : SmtDatatypeDecl) : List (List SmtType) :=
  dtConses (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd)

mutual
  /-- A value of a type of depth `d + 1` at most, by the first constructor
  with such values of its fields (each of least depth). -/
  def groundAt : Nat → SmtType → Option MVal
    | _, .Bool => some (.bool false)
    | _, .USort s => some (.uval s 0)
    | _, .Int => some (.int 0)
    | _, .Real => some (.rat 0)
    | 0, .Datatype s dd =>
      (consesOf s dd).zipIdx.findSome? fun (fs, i) =>
        if fs.isEmpty then some (MVal.mkDt s dd i []) else none
    | d + 1, .Datatype s dd =>
      (consesOf s dd).zipIdx.findSome? fun (fs, i) =>
        (fs.mapM (groundMin d)).map (MVal.mkDt s dd i)
    | _, _ => none
  termination_by d _ => (d, 0)

  /-- A value of a type of least depth, at most `d + 1`. -/
  def groundMin : Nat → SmtType → Option MVal
    | 0, T => groundAt 0 T
    | d + 1, T => (groundMin d T).orElse fun _ => groundAt (d + 1) T
  termination_by d _ => (d, 1)
end

/-- A value of a type: `false`, the first element of a sort, a datatype value
of least depth (within `fuel`; the first constructor among those of that
depth), so that it does not depend on the fuel. -/
def groundValue : Nat → SmtType → Option MVal
  | 0, _ => none
  | f + 1, T => groundMin f T

/-- The type has infinitely many values (within `fuel`): a sort, or a datatype
with a constructor that has a field of the datatype or of an infinite type. -/
def infiniteType : Nat → SmtType → Bool
  | 0, _ => false
  | _ + 1, .USort _ => true
  | _ + 1, .Int => true
  | _ + 1, .Real => true
  | f + 1, T@(.Datatype s dd) =>
    (consesOf s dd).any fun fs => fs.any fun F => F == T || infiniteType f F
  | _ + 1, _ => false

/-- The `k`-th value of a type, distinct for distinct `k` (for an infinite
type; for Booleans, `k` below 2): nesting a recursive constructor `k` times,
or varying an infinite field. -/
def valueAt : Nat → SmtType → Nat → Option MVal
  | 0, _, _ => none
  | _ + 1, .Bool, k => if k < 2 then some (.bool (k == 1)) else none
  | _ + 1, .USort s, k => some (.uval s k)
  | _ + 1, .Int, k => some (.int k)
  | _ + 1, .Real, k => some (.rat k)
  | f + 1, T@(.Datatype s dd), k =>
    let cs := (consesOf s dd).zipIdx
    match cs.find? (fun (fs, _) => fs.contains T) with
    | some (fs, i) =>
      if k == 0 then groundValue (f + 1) T else
      -- the first field of the datatype is the value before
      (fieldValues f T fs (valueAt f T (k - 1))).map (MVal.mkDt s dd i)
    | none =>
      match cs.find? (fun (fs, _) => fs.any (infiniteType f)) with
      | some (fs, i) =>
        let F := (fs.find? (infiniteType f)).getD .None
        (fieldValues f F fs (valueAt f F k)).map (MVal.mkDt s dd i)
      | none => if k == 0 then groundValue (f + 1) T else none
  | _ + 1, _, _ => none
where
  /-- The values of the fields `fs`: the first of type `F` is `v`, the others
  ground. -/
  fieldValues (f : Nat) (F : SmtType) (fs : List SmtType) (v : Option MVal) : Option (List MVal) :=
    let i := fs.idxOf F
    (fs.zipIdx.mapM fun (G, j) => if j == i then v else groundValue f G)

/-- The `k`-th value of a datatype whose top constructor is `i`. -/
def consValueAt (f : Nat) (s : native_String) (dd : SmtDatatypeDecl) (i k : Nat) : Option MVal :=
  let T := SmtType.Datatype s dd
  match (consesOf s dd)[i]? with
  | none => none
  | some fs =>
    let vary := if fs.contains T then some T else fs.find? (infiniteType f)
    match vary with
    | some F => (valueAt.fieldValues f F fs (valueAt f F k)).map (MVal.mkDt s dd i)
    | none => if k == 0 then (fs.mapM (groundValue f)).map (MVal.mkDt s dd i) else none

/-- The default value of a type, if it has one in the model. -/
def defaultValue (T : SmtType) : Option MVal :=
  match T with
  | .Bool => some (.bool false)
  | .USort s => some (.uval s 0)
  | .Int => some (.int 0)
  | .Real => some (.rat 0)
  | .Datatype .. => groundValue 16 T
  | .Set E => some (.sempty E)
  | .Seq .Char => some (.str [])
  | _ => none

/-- The function and arguments of an application of a declared function. -/
def ufApp? : Node → Option (String × TypeNode × Array Node)
  | .app (.node .APPLY_UF (.var f T)) cs => some (f, T, cs)
  | _ => none

/-- The range of a Logos function type after `k` arguments. -/
def rangeAfter : SmtType → Nat → SmtType
  | .FunType _ r, k + 1 => rangeAfter r k
  | T, _ => T

structure Builder where
  model : Model := {}
  /-- The table of each function symbol and each prefix of argument values. -/
  tables : Std.HashMap (String × List Nat) Nat := {}
  /-- The values, by index, for the keys of `tables`. -/
  valIndex : Array MVal := #[]

/-- A new table of type `d → r` with no entries; its default is the default of
`r`, or, for a function type, a new table with no entries. -/
def newTable (d r : SmtType) : Nat → StateM Builder (Option Nat)
  | 0 => pure none
  | fuel + 1 => do
    let dflt ← match r with
      | .FunType d' r' => do
        match ← newTable d' r' fuel with
        | some sub => pure (some (MVal.fn sub d' r'))
        | none => pure none
      | _ => pure (defaultValue r)
    let some dflt := dflt | return none
    modifyGet fun b =>
      let fid := b.model.funs.size
      (some fid, { b with model := { b.model with funs := b.model.funs.push ⟨d, r, [], dflt⟩ } })

/-- The index of a value, for the keys of the tables. -/
def valueIndex (v : MVal) : StateM Builder Nat := do
  match (← get).valIndex.idxOf? v with
  | some i => return i
  | none => modifyGet fun b => (b.valIndex.size, { b with valIndex := b.valIndex.push v })

/-- The table of `f` (of Logos type `T`) after the arguments `pre`, created if
needed. -/
def tableOf (f : String) (T : SmtType) (pre : List MVal) : StateM Builder (Option Nat) := do
  let key ← pre.mapM valueIndex
  if let some fid := (← get).tables.get? (f, key) then return some fid
  let .FunType d r := rangeAfter T pre.length | return none
  let some fid ← newTable d r 64 | return none
  modify fun b => { b with tables := b.tables.insert (f, key) fid }
  return some fid

/-- Add an entry to a table, if it has none for the argument. -/
def addToTable (fid : Nat) (a v : MVal) : StateM Builder Unit := do
  let funs ← modifyGet fun b => (b.model.funs, { b with model := { b.model with funs := #[] } })
  let funs := funs.modify fid fun t =>
    if t.entries.any (·.1.veq a) then t else { t with entries := t.entries ++ [(a, v)] }
  modify fun b => { b with model := { b.model with funs } }

/-- Record that `f` maps the arguments `args` to `v`. -/
def addEntry (f : String) (T : SmtType) (args : List MVal) (v : MVal) : StateM Builder Unit :=
  go [] args
where
  go (pre : List MVal) : List MVal → StateM Builder Unit
    | [] => pure ()
    | [a] => do
      let some fid ← tableOf f T pre | return
      addToTable fid a v
    | a :: rest => do
      let some fid ← tableOf f T pre | return
      let some sub ← tableOf f T (pre ++ [a]) | return
      let some t := (← get).model.funs[sub]? | return
      addToTable fid a (.fn sub t.dom t.rng)
      go (pre ++ [a]) rest

/-- The value of a class of the equality engine that is not a datatype's,
given by its representative. -/
def classValue (ee : EE.EqualityEngine) (rep : Nat) : Option MVal :=
  let t := ee.nodes[rep]!
  match t with
  | .const (.boolean b) => some (.bool b)
  | _ => match t.typeHint with
    | some .boolean => some (.bool false)
    | some (.sort s) => some (.uval s (rep + 1))
    | _ => none

/-- The constructor of a constructor term: of an application, or a nullary
constructor. -/
def consTerm? : Node → Option (native_String × SmtDatatypeDecl × Nat × Array Node)
  | .app (.node .APPLY_CONSTRUCTOR f) cs => (Model.consOf? f).map fun (s, dd, i) => (s, dd, i, cs)
  | t@(.const (.dtCons ..)) => (Model.consOf? t).map fun (s, dd, i) => (s, dd, i, #[])
  | _ => none

/-- **The values of the classes** of the equality engine, by representative,
as cvc5's model builder gives them (`TheoryDatatypes::collectModelInfo`): a
class of a datatype with a constructor term has the constructor applied to the
values of its arguments' classes; one with none (the theory did not need to
split it) a value of its own, distinct from the others', whose constructor is
not one its testers exclude; the others as `classValue`. -/
def classValues (ee : EE.EqualityEngine) (arith : Array (Node × Rat) := #[]) : Std.HashMap Nat MVal := Id.run do
  let n := ee.nodes.size
  let find (i : Nat) := EE.find ee i
  let id? (t : Node) : Option Nat := (ee.nodeIds.get? ⟨t⟩).map find
  -- the value of an arithmetic class: of a numeral in it, or of a term the
  -- arithmetic solver has a value of
  let arithVals : Std.HashMap Key Rat := arith.foldl (fun m (t, q) => m.insert ⟨t⟩ q) {}
  let mut arithOf : Std.HashMap Nat MVal := {}
  for h : i in [0:n] do
    if ee.isInternal[i]! then continue
    let t := ee.nodes[i]
    let r := find i
    if arithOf.contains r then continue
    let q? := match t with
      | .const (.integer k) => some (k : Rat)
      | .const (.rational q) => some q
      | _ => arithVals.get? ⟨t⟩
    if let some q := q? then
      arithOf := arithOf.insert r (if t.typeHint == some .integer then .int q.floor else .rat q)
  -- an arithmetic class with an application of arithmetic (no leaf) takes
  -- its value from those of the arguments' classes, as the model builder
  -- evaluates the terms that are not assignable
  let ratOf (v : MVal) : Option Rat := match v with
    | .int k => some k
    | .rat q => some q
    | _ => none
  let rec evalArith (vals : Std.HashMap Nat MVal) : Nat → Node → Option Rat
    | 0, _ => none
    | fuel + 1, t =>
      match t with
      | .const (.integer k) => some k
      | .const (.rational q) => some q
      | _ =>
      match (id? t).bind vals.get? |>.bind ratOf with
      | some q => some q
      | none =>
        match t with
        | .app (.kind k) cs => do
          let vs ← cs.toList.mapM (evalArith vals fuel)
          match k, vs with
          | .ADD, vs => some (vs.foldl (· + ·) 0)
          | .MULT, vs => some (vs.foldl (· * ·) 1)
          | .SUB, [a, b] => some (a - b)
          | .NEG, [a] => some (-a)
          | .TO_REAL, [a] => some a
          | .TO_INTEGER, [a] => some (a.floor : Int)
          | .ABS, [a] => some (if a < 0 then -a else a)
          | .DIVISION, [a, b] => if b == 0 then none else some (a / b)
          | _, _ => none
        | _ => none
  let mut changed := true
  while changed do
    changed := false
    for h : i in [0:n] do
      if ee.isInternal[i]! || arithOf.contains (find i) then continue
      let t := ee.nodes[i]
      let .app (.kind _) _ := t | continue
      if let some q := evalArith arithOf 64 t then
        arithOf := arithOf.insert (find i) (if t.typeHint == some .integer then .int q.floor else .rat q)
        changed := true
  -- an arithmetic class with no value gets a fresh one, distinct from the
  -- others (as the model builder's type enumerators do)
  let mut usedArith : Array MVal := arithOf.fold (fun acc _ v => acc.push v) #[]
  for h : i in [0:n] do
    if ee.isInternal[i]! || find i != i || arithOf.contains i then continue
    let t := ee.nodes[i]
    let isInt := t.typeHint == some .integer
    if !(isInt || t.typeHint == some .real) then continue
    let mut k : Int := 0
    while usedArith.contains (if isInt then .int k else .rat k) do k := k + 1
    let v : MVal := if isInt then .int k else .rat k
    arithOf := arithOf.insert i v
    usedArith := usedArith.push v
  -- the strings (`TheoryStrings::collectModelValues`): a class with a
  -- constant has it; a class whose normal form (of the last full-effort
  -- check) is one non-constant component, or which has none, is atomic, and
  -- has a string of its length (the value of its length term's class) of its
  -- own; another has the concatenation of the values of its normal form's
  -- components
  let mut strConst : Std.HashMap Nat (List Nat) := {}
  let mut lenClass : Std.HashMap Nat Nat := {}
  for h : i in [0:n] do
    if ee.isInternal[i]! then continue
    match ee.nodes[i] with
    | .const (.string w) => strConst := strConst.insert (find i) w
    | .app (.kind .STRING_LENGTH) #[a] =>
      if let some r := id? a then lenClass := lenClass.insert r (find i)
    | _ => pure ()
  let strNf (r : Nat) : Option (Array Node) :=
    (ee.strings.chk.normalForms.get? ⟨ee.nodes[r]!⟩).map (·.nf)
  let isAtomic (r : Nat) : Bool :=
    !strConst.contains r && match strNf r with
      | none => true
      | some nf => nf.size == 1 && !nf[0]!.isConst
  let lenOf (r : Nat) : Option Nat :=
    match (lenClass.get? r).bind arithOf.get? with
    | some (.int k) => some k.toNat
    | _ => none
  let mut usedStr : Array (List Nat) := strConst.fold (fun acc _ w => acc.push w) #[]
  let mut strOf : Std.HashMap Nat (List Nat) := strConst
  -- a class of length one with a code term: the character of the code's value
  -- (`hasStringCode`)
  for h : i in [0:n] do
    if ee.isInternal[i]! || find i != i || ee.nodes[i].typeHint != some .string || !isAtomic i then continue
    if lenOf i != some 1 then continue
    let some a := (ee.strings.getEqcInfo? ee.nodes[i]).bind (·.codeTerm) | continue
    match (id? (Node.mkNode .STRING_TO_CODE #[a])).bind arithOf.get? with
    | some (.int c) =>
      if c ≥ 0 then
        strOf := strOf.insert i [c.toNat]
        usedStr := usedStr.push [c.toNat]
    | _ => pure ()
  for h : i in [0:n] do
    if ee.isInternal[i]! || find i != i || ee.nodes[i].typeHint != some .string || !isAtomic i then continue
    if strOf.contains i then continue
    -- the first string, by length then in order, of letters from `a`
    let start := (lenOf i).getD 0
    -- (a string too long to write down has no value: the model is then not
    -- evaluated)
    if start > 1000000 then continue
    let mut found : Option (List Nat) := none
    for L in [start : start + 8] do
      if found.isSome then break
      let count := 26 ^ L
      for k in [0 : min count 4096] do
        let w := (List.range L).map fun j => 97 + (k / 26 ^ (L - 1 - j)) % 26
        if !usedStr.contains w then
          found := some w
          break
      if (lenOf i).isSome then break
    if let some w := found then
      strOf := strOf.insert i w
      usedStr := usedStr.push w
  -- the other classes: their normal forms' components, in turn
  let mut strChanged := true
  while strChanged do
    strChanged := false
    for h : i in [0:n] do
      if ee.isInternal[i]! || find i != i || ee.nodes[i].typeHint != some .string || strOf.contains i then continue
      let some nf := strNf i | continue
      let ws := nf.toList.mapM fun c => match c with
        | .const (.string w) => some w
        | _ => (id? c).bind strOf.get?
      if let some ws := ws then
        strOf := strOf.insert i ws.flatten
        strChanged := true
  -- a constructor term of each class, and the constructors its testers exclude
  let mut cons : Std.HashMap Nat Nat := {}
  let mut excluded : Std.HashMap Nat (List Nat) := {}
  let falseRep := id? Node.mkFalse
  for h : i in [0:n] do
    if ee.isInternal[i]! then continue
    let t := ee.nodes[i]
    if (consTerm? t).isSome && !cons.contains (find i) then cons := cons.insert (find i) i
    if let .app (.node .APPLY_TESTER f) #[x] := t then
      if some (find i) == falseRep then
        if let (some (_, _, c), some r) := (Model.consOf? f, id? x) then
          excluded := excluded.insert r (c :: excluded.getD r [])
  -- a class of a datatype with selector terms but no constructor term has a
  -- constructor applied to its selector terms (`getInstCons`, the constructors
  -- with an infinite field first): the values of their classes, or fresh ones
  -- for the fields with no selector term
  let mut selTerms : Std.HashMap Nat (List (Nat × Nat × Nat)) := {}
  for h : i in [0:n] do
    if ee.isInternal[i]! then continue
    if let .app (.node .APPLY_SELECTOR f) #[x] := ee.nodes[i] then
      if let (some (_, _, c, j), some r) := (Model.selOf? f, id? x) then
        if !cons.contains r then selTerms := selTerms.insert r ((c, j, find i) :: selTerms.getD r [])
  let infField (F : SmtType) : Bool := infiniteType 16 F
  let mut virtual : Std.HashMap Nat (native_String × SmtDatatypeDecl × Nat × List (Sum Nat MVal)) := {}
  for (r, sels) in selTerms.toList do
    let some T := ee.nodes[r]!.typeHint.map fun T => __eo_to_smt_type T.toEo | continue
    let .Datatype s dd := T | continue
    let conses := consesOf s dd
    let ex := excluded.getD r []
    let allowed := (List.range conses.length).filter (!ex.contains ·)
    let inf := allowed.filter fun c => (conses[c]!).any fun F => F == T || infField F
    let some c := (inf ++ allowed.filter (!inf.contains ·)).head? | continue
    let mut fields : List (Sum Nat MVal) := []
    let mut ok := true
    for (F, j) in (conses[c]!).zipIdx do
      match sels.find? fun (c', j', _) => c' == c && j' == j with
      | some (_, _, cls) => fields := fields ++ [.inl cls]
      | none =>
        if F == .Int || F == .Real then
          let mut k : Int := 0
          let mk := fun (k : Int) => if F == .Int then MVal.int k else MVal.rat k
          while usedArith.contains (mk k) do k := k + 1
          usedArith := usedArith.push (mk k)
          fields := fields ++ [.inr (mk k)]
        else match groundValue 16 F with
          | some v => fields := fields ++ [.inr v]
          | none => ok := false
    if ok then virtual := virtual.insert r (s, dd, c, fields)
  -- the members of each class of sets (`getMembers`, from the membership
  -- atoms that are true), by representative
  let trueRep := id? Node.mkTrue
  let mut members : Std.HashMap Nat (List Nat) := {}
  for h : i in [0:n] do
    if ee.isInternal[i]! then continue
    if let .app (.kind .SET_MEMBER) #[x, S] := ee.nodes[i] then
      if trueRep.isSome && some (find i) == trueRep then
        if let (some xr, some sr) := (id? x, id? S) then
          let ms := members.getD sr []
          if !ms.contains xr then members := members.insert sr (ms ++ [xr])
  -- the values, from those of the classes without constructor terms (`fresh`)
  let rec value (fuel : Nat) (fresh : Std.HashMap Nat MVal) (r : Nat) : Option MVal :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match cons.get? r with
      | some i =>
        match consTerm? ee.nodes[i]! with
        | some (s, dd, c, cs) =>
          (cs.toList.mapM fun x => (id? x).bind (value fuel fresh)).map (MVal.mkDt s dd c)
        | none => none
      | none =>
      match virtual.get? r with
      | some (s, dd, c, fields) =>
        (fields.mapM fun (x : Sum Nat MVal) => match x with | .inl cls => value fuel fresh cls | .inr v => some v).map (MVal.mkDt s dd c)
      | none =>
        match ee.nodes[r]!.typeHint.map fun T => __eo_to_smt_type T.toEo with
        | some (.Datatype ..) => fresh.get? r
        | some .Real | some .Int => arithOf.get? r
        | some (.Seq .Char) => (strOf.get? r).map .str
        | some (.Set E) =>
          -- a set: the values of its members (`collectModelValues`)
          ((members.getD r []).mapM (value fuel fresh)).map (MVal.sempty E).insAll
        | _ => classValue ee r
  let reps := (List.range n).filter fun i => !ee.isInternal[i]! && find i == i
  let dtRep (r : Nat) : Option (native_String × SmtDatatypeDecl) :=
    match ee.nodes[r]!.typeHint.map fun T => __eo_to_smt_type T.toEo with
    | some (.Datatype s dd) => some (s, dd)
    | _ => none
  -- the values that do not depend on fresh ones are taken
  let mut used : Array MVal := #[]
  for r in reps do
    if let some v := value 64 {} r then
      if (dtRep r).isSome then used := used.push v
  -- a fresh value for each class without a constructor term, which makes no
  -- two classes equal that were not (the classes whose values depend on it,
  -- such as `(cons x t)` for a fresh `t`, included)
  let dtReps := reps.filter fun r => (dtRep r).isSome
  let collisions (fresh : Std.HashMap Nat MVal) : Nat := Id.run do
    let vs := dtReps.filterMap (value 64 fresh)
    let mut seen : Array MVal := #[]
    let mut k := 0
    for v in vs do
      if seen.contains v then k := k + 1 else seen := seen.push v
    return k
  let mut fresh : Std.HashMap Nat MVal := {}
  let mut base := collisions fresh
  for r in reps do
    if cons.contains r || virtual.contains r then continue
    let some (s, dd) := dtRep r | continue
    let ex := excluded.getD r []
    let allowed := (List.range (consesOf s dd).length).filter (!ex.contains ·)
    let mut found : Option MVal := none
    for k in [0:64] do
      if found.isSome then break
      for c in allowed do
        if let some v := consValueAt 16 s dd c k then
          if !used.contains v then
            let n := collisions (fresh.insert r v)
            if n ≤ base then
              found := some v
              base := n
              break
    if let some v := found then
      fresh := fresh.insert r v
      used := used.push v
  let mut out : Std.HashMap Nat MVal := {}
  for r in reps do
    if let some v := value 64 fresh r then out := out.insert r v
  return out

/-- The selectors applied in nodes. -/
partial def selectorsOf (ns : List Node) : List (native_String × SmtDatatypeDecl × Nat × Nat) :=
  let rec go (n : Node) : StateM (Std.HashSet Key × Array (native_String × SmtDatatypeDecl × Nat × Nat)) Unit := do
    if (← get).1.contains ⟨n⟩ then return
    modify fun (s, a) => (s.insert ⟨n⟩, a)
    if let .app (.node .APPLY_SELECTOR f) _ := n then
      if let some sel := Model.selOf? f then
        modify fun (s, a) => (s, if a.contains sel then a else a.push sel)
    if let .app _ cs := n then for c in cs do go c
  ((ns.forM go).run ({}, #[])).2.2.toList

/-- The function of division by zero of a skolem (cvc5's `@int_div_by_zero`,
`@mod_by_zero`, `@div_by_zero`): Logos's name for it and its type. -/
def byZeroFn : SkolemId → Option (native_String × SmtType)
  | .INT_DIV_BY_ZERO => some (Model.divByZeroName, .FunType .Int .Int)
  | .MOD_BY_ZERO => some (Model.modByZeroName, .FunType .Int .Int)
  | .DIV_BY_ZERO => some (Model.qdivByZeroName, .FunType .Real .Real)
  | _ => none

/-- The functions of division by zero that the divisions of `ns` use. -/
partial def byZeroOf (ns : List Node) : List (native_String × SmtType) :=
  let rec go (n : Node) : StateM (Std.HashSet Key × Array (native_String × SmtType)) Unit := do
    if (← get).1.contains ⟨n⟩ then return
    modify fun (s, a) => (s.insert ⟨n⟩, a)
    let f : Option (native_String × SmtType) := match n.getKind with
      | .INTS_DIVISION => byZeroFn .INT_DIV_BY_ZERO
      | .INTS_MODULUS => byZeroFn .MOD_BY_ZERO
      | .DIVISION => byZeroFn .DIV_BY_ZERO
      | _ => none
    if let some fT := f then modify fun (s, a) => (s, if a.contains fT then a else a.push fT)
    if let .app _ cs := n then for c in cs do go c
  ((ns.forM go).run ({}, #[])).2.2.toList

/-- Set the value of a constant. -/
def setConst (x : String) (T : TypeNode) (v : MVal) (b : Builder) : Builder :=
  { b with model := { b.model with consts := b.model.consts.insert (keyName x) (tyS T, v) } }

/-- The relevant terms (`Theory::computeRelevantTerms`): the subterms of the
asserted literals. Model construction considers only these, as cvc5's model
equality engine does. -/
partial def relevantTerms (asserted : Array Node) : Std.HashSet Key :=
  let rec go (n : Node) : StateM (Std.HashSet Key) Unit := do
    if (← get).contains ⟨n⟩ then return
    modify (·.insert ⟨n⟩)
    match n with
    | .app _ cs => for c in cs do go c
    | _ => pure ()
  ((asserted.forM go).run {}).2

/-- **Build a model** from the equality engine's classes of the relevant terms
`relevant`, for the free constants `syms` of the input assertions `inputs`,
and the definitions `defs` (`x := t`) of the variables solved by
preprocessing, in order; the Boolean variables the equality engine does not
have get their values from the literals `asserted` (the SAT solver's). -/
def buildModel (ee : EE.EqualityEngine) (relevant : Std.HashSet Key) (syms : List Node)
    (defs : List (Node × Node)) (inputs : List Node)
    (arith : Array (Node × Rat) := #[]) (asserted : Array Node := #[]) : Model := Id.run do
  let mut b : Builder := {}
  let vals := classValues ee arith
  let valOf (t : Node) : Option MVal := (ee.nodeIds.get? ⟨t⟩).bind fun j => vals.get? (EE.find ee j)
  -- the functions of the wrong applications of selectors: their keys
  let mut wrong : Array (String × native_String × SmtType) := #[]
  -- the constants and applications of the engine that are relevant
  for h : i in [0:ee.nodes.size] do
    if ee.isInternal[i]! then continue
    let t := ee.nodes[i]
    if !relevant.contains ⟨t⟩ then continue
    let some v := vals.get? (EE.find ee i) | continue
    match t with
    | .var x T => b := setConst x T v b
    | .app (.node .APPLY_SELECTOR f) #[x] =>
      -- a selector applied to another constructor: an entry of the function
      -- of its wrong applications
      if let (some (s, dd, c, j), some vx) := (Model.selOf? f, valOf x) then
        if vx.head != .dtc s dd c then
          let key := s!"\u0000wrong {c} {j} " ++ String.ofList (s.map Char.ofNat)
          let T := Model.wrongSelType s dd c j
          if !wrong.any (·.1 == key) then wrong := wrong.push (key, Model.wrongSelName c j, T)
          b := ((addEntry key T [vx] v).run b).2
    | .app (.node .APPLY_UF (.skolem id #[])) #[x] =>
      -- a division by zero: an entry of Logos's function of it
      if let (some (name, T), some vx) := (byZeroFn id, valOf x) then
        let key := "\u0000byzero " ++ String.ofList (name.map Char.ofNat)
        if !wrong.any (·.1 == key) then wrong := wrong.push (key, name, T)
        b := ((addEntry key T [vx] v).run b).2
    | _ => match ufApp? t with
      | some (f, T, cs) =>
        let args := cs.toList.filterMap valOf
        if args.length == cs.size then
          b := ((addEntry f (tyS T) args v).run b).2
      | none => pure ()
  -- every selector applied in the input has one, so that each of its
  -- applications evaluates (to the table's default when the engine has no
  -- entry)
  -- every function of division by zero the input uses has one, too
  for (name, T) in byZeroOf inputs do
    let key := "\u0000byzero " ++ String.ofList (name.map Char.ofNat)
    if !wrong.any (·.1 == key) then wrong := wrong.push (key, name, T)
  for (s, dd, c, j) in selectorsOf inputs do
    let key := s!"\u0000wrong {c} {j} " ++ String.ofList (s.map Char.ofNat)
    if !wrong.any (·.1 == key) then wrong := wrong.push (key, Model.wrongSelName c j, Model.wrongSelType s dd c j)
  for (key, name, T) in wrong do
    let (fid, b') := (tableOf key T []).run b
    b := b'
    if let some fid := fid then
      let t := b.model.funs[fid]!
      b := { b with model := { b.model with others := b.model.others.push (name, T, .fn fid t.dom t.rng) } }
  -- the function symbols: their top table
  for f in syms do
    if let .var x T := f then
      if let .function _ _ := T then
        let (fid, b') := (tableOf x (tyS T) []).run b
        b := b'
        if let some fid := fid then
          let t := b.model.funs[fid]!
          b := setConst x T (.fn fid t.dom t.rng) b
  -- the arithmetic solver's values of its variables
  for (x, q) in arith do
    if let .var name T := x then
      b := setConst name T (if T == .integer then .int q.floor else .rat q) b
  -- the Boolean variables the SAT solver assigned (not in the equality engine)
  for l in asserted do
    match l with
    | .var name .boolean =>
      if (b.model.const name .boolean).isNone then b := setConst name .boolean (.bool true) b
    | .app (.kind .NOT) #[.var name .boolean] =>
      if (b.model.const name .boolean).isNone then b := setConst name .boolean (.bool false) b
    | _ => pure ()
  -- the other constants: the defaults of those not defined, then the
  -- definitions (which may use them), then the defaults of the rest
  let defined := defs.map (·.1)
  for x in syms do
    if let .var name T := x then
      if (b.model.const name T).isNone && !defined.contains x then
        if let some v := defaultValue (tyS T) then b := setConst name T v b
  -- (in passes: a definition may use one that comes later)
  let mut pending := defs
  for _ in [0:defs.length] do
    if pending.isEmpty then break
    let mut rest := []
    for (x, t) in pending do
      if let .var name T := x then
        match b.model.eval t with
        | some v => b := setConst name T v b
        | none => rest := rest ++ [(x, t)]
    pending := rest
  for x in syms do
    if let .var name T := x then
      if (b.model.const name T).isNone then
        if let some v := defaultValue (tyS T) then b := setConst name T v b
  return b.model

/-- The free constants of nodes. -/
partial def freeConsts (ns : List Node) : List Node :=
  let rec go (n : Node) : StateM (Std.HashSet Key × Array Node) Unit := do
    if (← get).1.contains ⟨n⟩ then return
    modify fun (s, a) => (s.insert ⟨n⟩, a)
    match n with
    | .var .. => modify fun (s, a) => (s, a.push n)
    | .app op cs => do
      if let .node _ f := op then go f
      for c in cs do go c
    | .skolem _ cs => for c in cs do go c
    | _ => pure ()
  ((ns.forM go).run ({}, #[])).2.2.toList

end Telos.Solver
