import Telos.Node.Node
import Cpc.SmtTranslate
import Cpc.SmtTyping
import Cpc.LogosTerm

/-!
# Translation to Logos terms

`Node.toEo` gives every node its meaning: the SMT-LIB semantics of a node is the
Logos semantics of its translation (`eo_satisfiability`, through `__eo_to_smt`).
This file is therefore part of the **specification** and is listed in
`TRUSTED.md`. Keep it a direct, structural transcription of how cvc5 prints a node
in CPC, so it is easy to audit.

The encoding follows the CPC signature (`Cpc.eo`) as Ethos elaborates it:

* `and`/`or` are `:right-assoc-nil` with nil `true`/`false`, so
  `(and a b c)` is `(and a (and b (and c true)))`.
* `=`, `=>`, `xor`, `not` and `ite` have the fixed arities of cvc5's kinds.
* `(distinct a b c)` is `(distinct (@@TypedList_cons a (@@TypedList_cons b
  (@@TypedList_cons c (@@TypedList_nil T)))))`, with `T` the type of `a`.
* Indexed operators become Logos's `UOp1`/`UOp2` with numeral indices:
  `((_ extract i j) x)` is `Term.Apply (Term.UOp2 UserOp2.extract i j) x`.
* `(f a b)` is the curried `((f a) b)`, and `(-> A B C)` is `(-> A (-> B C))`.
* `(forall ((x T) …) F)` is `(forall (@list x …) F)`, where the bound variables are
  `Term.Var`s. Instantiation patterns are dropped.
* A declared constant is a `Term.UConst`, as in cvc5's proofs, numbered by its
  name (`constId`). Logos's checker treats these as closed (unlike `Term.Var`),
  which proofs by contradiction need: it pushes only closed assumptions.

A node with the wrong number of children or indices translates to `Term.Stuck`,
which has no SMT type, so it is not `WellTyped`.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- `(op x)` -/
def eoApp1 (op : UserOp) (x : Term) : Term :=
  Term.Apply (Term.UOp op) x

/-- `(op x y)` -/
def eoApp2 (op : UserOp) (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) x) y

/-- `(op x₁ (op x₂ … (op xₙ nil)))`: a `:right-assoc-nil` application. -/
def eoRightAssocNil (op : UserOp) (nil : Term) : List Term → Term
  | [] => nil
  | x :: xs => eoApp2 op x (eoRightAssocNil op nil xs)

/-- An Eunoia list `(@list x₁ … xₙ)`, as used for binder variable lists. -/
def eoList : List Term → Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoList xs)

namespace TypeNode

mutual

def toEo : TypeNode → Term
  | .boolean => Term.Bool
  | .integer => Term.UOp UserOp.Int
  | .real => Term.UOp UserOp.Real
  | .string => Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  | .regExp => Term.UOp UserOp.RegLan
  | .bitVector w => Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)
  | .array i e => Term.Apply (Term.Apply (Term.UOp UserOp.Array) i.toEo) e.toEo
  | .sequence e => Term.Apply (Term.UOp UserOp.Seq) e.toEo
  | .set e => Term.Apply (Term.UOp UserOp.Set) e.toEo
  | .function a r => Term.Apply (Term.Apply Term.FunType a.toEo) r.toEo
  | .sort id => Term.USort id
  | .datatype s d => Term.DatatypeType (native_string_lit s) (DtDecl.toEo d)
  | .typeRef s => Term.DatatypeTypeRef (native_string_lit s)

def _root_.Telos.DtDecl.toEo : DtDecl → DatatypeDecl
  | .nil => .nil
  | .cons s d rest => .cons (native_string_lit s) (Dt.toEo d) (DtDecl.toEo rest)

def _root_.Telos.Dt.toEo : Dt → Datatype
  | .null => .null
  | .sum c rest => .sum (DtCons.toEo c) (Dt.toEo rest)

def _root_.Telos.DtCons.toEo : DtCons → DatatypeCons
  | .unit => .unit
  | .cons f rest => .cons (toEo f) (DtCons.toEo rest)

end

end TypeNode

namespace Const

def toEo : Const → Term
  | .boolean b => Term.Boolean b
  | .integer n => Term.Numeral n
  | .rational q => Term.Rational q
  | .bitVector w v => Term.Binary w v
  | .string s => Term.String s
  | .emptySet T => Term.UOp1 UserOp1.set_empty (TypeNode.set T).toEo
  | .dtCons (.datatype s d) i => Term.DtCons (native_string_lit s) d.toEo i
  | .dtSel (.datatype s d) i j => Term.DtSel (native_string_lit s) d.toEo i j
  | .dtCons .. | .dtSel .. => Term.Stuck

end Const

/-- How many children an application takes. -/
inductive Arity where
  | exactly (n : Nat)
  | atLeast (n : Nat)
  deriving DecidableEq, Repr

def Arity.accepts : Arity → Nat → Bool
  | .exactly n, m => m == n
  | .atLeast n, m => n ≤ m

namespace TypeNode

mutual

/-- The type of a Logos SMT type, if `TypeNode` has one for it. -/
def ofSmt : SmtType → Option TypeNode
  | .Bool => some .boolean
  | .Int => some .integer
  | .Real => some .real
  | .RegLan => some .regExp
  | .BitVec w => some (.bitVector w)
  | .Seq .Char => some .string
  | .Seq e => .sequence <$> ofSmt e
  | .Set e => .set <$> ofSmt e
  | .Map i e => .array <$> ofSmt i <*> ofSmt e
  | .FunType a r => .function <$> ofSmt a <*> ofSmt r
  | .USort i => some (.sort i)
  | .Datatype s d => .datatype (String.ofList (s.map Char.ofNat)) <$> dtDeclOfSmt d
  | .TypeRef s => some (.typeRef (String.ofList (s.map Char.ofNat)))
  | _ => none

def dtDeclOfSmt : SmtDatatypeDecl → Option DtDecl
  | .nil => some .nil
  | .cons s d rest =>
    .cons (String.ofList (s.map Char.ofNat)) <$> dtOfSmt d <*> dtDeclOfSmt rest

def dtOfSmt : SmtDatatype → Option Dt
  | .null => some .null
  | .sum c rest => .sum <$> dtConsOfSmt c <*> dtOfSmt rest

def dtConsOfSmt : SmtDatatypeCons → Option DtCons
  | .unit => some .unit
  | .cons f rest => .cons <$> ofSmt f <*> dtConsOfSmt rest

end

/-- The CPC type term of a Logos SMT type, and `Term.Stuck` if it has none. -/
def eoOfSmt (T : SmtType) : Term :=
  match ofSmt T with
  | some T => T.toEo
  | none => Term.Stuck

end TypeNode

/-- The nil terminator of a typed `:right-assoc-nil` operator (or of the typed
list of `distinct`) whose elements have SMT type `T`, as `Cpc.eo` declares it
(`:right-assoc-nil` attributes). `Term.Stuck` on any other type, so the
application is not well typed.

This table is written out here rather than taken from Logos's `__eo_nil` and
`__eo_typeof`, to keep Eunoia's type inference out of the trusted base; the
element type comes from `__smtx_typeof`, which the specification already relies
on (`WellTyped`). Logos's `__eo_nil` agrees with it on well-typed elements, up
to bit-vector widths above 2^32, where `__eo_to_bin` is stuck. -/
def typedNilOfType : UserOp → SmtType → Term
  | .plus, .Int => Term.Numeral 0
  | .plus, .Real => Term.Rational (native_mk_rational 0 1)
  | .mult, .Int => Term.Numeral 1
  | .mult, .Real => Term.Rational (native_mk_rational 1 1)
  | .concat, .BitVec _ => Term.Binary 0 0
  | .bvand, .BitVec w => Term.Binary w (2 ^ w - 1)
  | .bvor, .BitVec w => Term.Binary w 0
  | .bvxor, .BitVec w => Term.Binary w 0
  | .bvadd, .BitVec w => Term.Binary w 0
  | .bvmul, .BitVec w => Term.Binary w (1 % 2 ^ w)
  | .str_concat, .Seq .Char => Term.String []
  | .str_concat, .Seq E => Term.UOp1 UserOp1.seq_empty (TypeNode.eoOfSmt (.Seq E))
  | ._at__at_TypedList_cons, T =>
      if T = .None then Term.Stuck
      else Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (TypeNode.eoOfSmt T)
  | _, _ => Term.Stuck

/-- The nil terminator of a `:right-assoc-nil` operator. -/
inductive Nil where
  /-- The same nil for every type, like `true` for `and`. -/
  | const (t : Term)
  /-- The nil for the type of the first element (`typedNilOfType`), like `0` or
  `0.0` for `+`. -/
  | typed

/-- The nil of `op` for a list whose first element is `x`, from its SMT type. -/
def typedNil (op : UserOp) (x : Term) : Term :=
  typedNilOfType op (__smtx_typeof (__eo_to_smt x))

/-- The nil of `op` for a list whose first element is `x`. -/
def Nil.eval (op : UserOp) : Nil → Term → Term
  | .const t, _ => t
  | .typed, x => typedNil op x

/-- How an application is written in CPC. Every operator is described by one of
these shapes, so the translation (and its congruence proof) is uniform. -/
inductive AppShape where
  /-- `(head x₁ … xₙ)`, curried: `Apply (… (Apply head x₁) …) xₙ`. -/
  | spine (head : Term) (arity : Arity)
  /-- A `:right-assoc-nil` operator: `(op x₁ (op x₂ … (op xₙ nil)))`, n ≥ 2. The
  nil terminator is computed from the type of the first element `x₁`, as Logos's
  parser and Eunoia do (`Nil.eval`). -/
  | rightAssocNil (op : UserOp) (nil : Nil)
  /-- An operator applied to a typed argument list, `(op (@@TypedList_cons x₁ …
  (@@TypedList_cons xₙ nil)))`, n ≥ 2, with the nil computed from `x₁` as for
  `rightAssocNil … .typed`. This is how Logos's parser reads `(distinct x₁ … xₙ)`. -/
  | typedList (op : UserOp)
  /-- A binder variable list `(@list x₁ … xₙ)`. -/
  | binderList
  /-- A binder `(op vars body)`, with optional instantiation patterns (dropped). -/
  | binder (op : UserOp)
  /-- No CPC counterpart; translates to `Term.Stuck`. -/
  | none

/-- The CPC form of each operator kind. This table is the heart of the
specification for operator kinds; keep it in line with `Cpc.eo`. -/
def Kind.eoShape : Kind → AppShape
  | .EQUAL => .spine (Term.UOp UserOp.eq) (.exactly 2)
  | .NOT => .spine (Term.UOp UserOp.not) (.exactly 1)
  | .AND => .rightAssocNil UserOp.and (.const (Term.Boolean true))
  | .OR => .rightAssocNil UserOp.or (.const (Term.Boolean false))
  | .IMPLIES => .spine (Term.UOp UserOp.imp) (.exactly 2)
  | .XOR => .spine (Term.UOp UserOp.xor) (.exactly 2)
  | .ITE => .spine (Term.UOp UserOp.ite) (.exactly 3)
  | .ADD => .rightAssocNil UserOp.plus .typed
  | .MULT => .rightAssocNil UserOp.mult .typed
  | .SUB => .spine (Term.UOp UserOp.neg) (.exactly 2)
  | .NEG => .spine (Term.UOp UserOp.__eoo_neg_2) (.exactly 1)
  | .DIVISION => .spine (Term.UOp UserOp.qdiv) (.exactly 2)
  | .INTS_DIVISION => .spine (Term.UOp UserOp.div) (.exactly 2)
  | .INTS_MODULUS => .spine (Term.UOp UserOp.mod) (.exactly 2)
  | .DIVISION_TOTAL => .spine (Term.UOp UserOp.qdiv_total) (.exactly 2)
  | .INTS_DIVISION_TOTAL => .spine (Term.UOp UserOp.div_total) (.exactly 2)
  | .INTS_MODULUS_TOTAL => .spine (Term.UOp UserOp.mod_total) (.exactly 2)
  | .ABS => .spine (Term.UOp UserOp.abs) (.exactly 1)
  | .LT => .spine (Term.UOp UserOp.lt) (.exactly 2)
  | .LEQ => .spine (Term.UOp UserOp.leq) (.exactly 2)
  | .GT => .spine (Term.UOp UserOp.gt) (.exactly 2)
  | .GEQ => .spine (Term.UOp UserOp.geq) (.exactly 2)
  | .TO_REAL => .spine (Term.UOp UserOp.to_real) (.exactly 1)
  | .TO_INTEGER => .spine (Term.UOp UserOp.to_int) (.exactly 1)
  | .IS_INTEGER => .spine (Term.UOp UserOp.is_int) (.exactly 1)
  | .POW2 => .spine (Term.UOp UserOp.int_pow2) (.exactly 1)
  | .INTS_LOG2 => .spine (Term.UOp UserOp.int_log2) (.exactly 1)
  | .INTS_ISPOW2 => .spine (Term.UOp UserOp.int_ispow2) (.exactly 1)
  | .DISTINCT => .typedList UserOp.distinct
  | .SELECT => .spine (Term.UOp UserOp.select) (.exactly 2)
  | .STRING_CONCAT => .rightAssocNil UserOp.str_concat .typed
  | .REGEXP_CONCAT => .rightAssocNil UserOp.re_concat (.const (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
  | .REGEXP_INTER => .rightAssocNil UserOp.re_inter (.const (Term.UOp UserOp.re_all))
  | .REGEXP_UNION => .rightAssocNil UserOp.re_union (.const (Term.UOp UserOp.re_none))
  | .STRING_LENGTH => .spine (Term.UOp UserOp.str_len) (.exactly 1)
  | .STRING_SUBSTR => .spine (Term.UOp UserOp.str_substr) (.exactly 3)
  | .STRING_UPDATE => .spine (Term.UOp UserOp.str_update) (.exactly 3)
  | .STRING_CHARAT => .spine (Term.UOp UserOp.str_at) (.exactly 2)
  | .STRING_CONTAINS => .spine (Term.UOp UserOp.str_contains) (.exactly 2)
  | .STRING_LT => .spine (Term.UOp UserOp.str_lt) (.exactly 2)
  | .STRING_LEQ => .spine (Term.UOp UserOp.str_leq) (.exactly 2)
  | .STRING_INDEXOF => .spine (Term.UOp UserOp.str_indexof) (.exactly 3)
  | .STRING_INDEXOF_RE => .spine (Term.UOp UserOp.str_indexof_re) (.exactly 3)
  | .STRING_REPLACE => .spine (Term.UOp UserOp.str_replace) (.exactly 3)
  | .STRING_REPLACE_ALL => .spine (Term.UOp UserOp.str_replace_all) (.exactly 3)
  | .STRING_REPLACE_RE => .spine (Term.UOp UserOp.str_replace_re) (.exactly 3)
  | .STRING_REPLACE_RE_ALL => .spine (Term.UOp UserOp.str_replace_re_all) (.exactly 3)
  | .STRING_PREFIX => .spine (Term.UOp UserOp.str_prefixof) (.exactly 2)
  | .STRING_SUFFIX => .spine (Term.UOp UserOp.str_suffixof) (.exactly 2)
  | .STRING_IS_DIGIT => .spine (Term.UOp UserOp.str_is_digit) (.exactly 1)
  | .STRING_ITOS => .spine (Term.UOp UserOp.str_from_int) (.exactly 1)
  | .STRING_STOI => .spine (Term.UOp UserOp.str_to_int) (.exactly 1)
  | .STRING_TO_CODE => .spine (Term.UOp UserOp.str_to_code) (.exactly 1)
  | .STRING_FROM_CODE => .spine (Term.UOp UserOp.str_from_code) (.exactly 1)
  | .STRING_TO_LOWER => .spine (Term.UOp UserOp.str_to_lower) (.exactly 1)
  | .STRING_TO_UPPER => .spine (Term.UOp UserOp.str_to_upper) (.exactly 1)
  | .STRING_REV => .spine (Term.UOp UserOp.str_rev) (.exactly 1)
  | .STRING_TO_REGEXP => .spine (Term.UOp UserOp.str_to_re) (.exactly 1)
  | .STRING_IN_REGEXP => .spine (Term.UOp UserOp.str_in_re) (.exactly 2)
  | .REGEXP_NONE => .spine (Term.UOp UserOp.re_none) (.exactly 0)
  | .REGEXP_ALL => .spine (Term.UOp UserOp.re_all) (.exactly 0)
  | .REGEXP_ALLCHAR => .spine (Term.UOp UserOp.re_allchar) (.exactly 0)
  | .REGEXP_DIFF => .spine (Term.UOp UserOp.re_diff) (.exactly 2)
  | .REGEXP_STAR => .spine (Term.UOp UserOp.re_mult) (.exactly 1)
  | .REGEXP_PLUS => .spine (Term.UOp UserOp.re_plus) (.exactly 1)
  | .REGEXP_OPT => .spine (Term.UOp UserOp.re_opt) (.exactly 1)
  | .REGEXP_RANGE => .spine (Term.UOp UserOp.re_range) (.exactly 2)
  | .REGEXP_COMPLEMENT => .spine (Term.UOp UserOp.re_comp) (.exactly 1)
  | .STORE => .spine (Term.UOp UserOp.store) (.exactly 3)
  | .SET_SINGLETON => .spine (Term.UOp UserOp.set_singleton) (.exactly 1)
  | .SET_UNION => .spine (Term.UOp UserOp.set_union) (.exactly 2)
  | .SET_INTER => .spine (Term.UOp UserOp.set_inter) (.exactly 2)
  | .SET_MINUS => .spine (Term.UOp UserOp.set_minus) (.exactly 2)
  | .SET_MEMBER => .spine (Term.UOp UserOp.set_member) (.exactly 2)
  | .SET_SUBSET => .spine (Term.UOp UserOp.set_subset) (.exactly 2)
  | .SET_CHOOSE => .spine (Term.UOp UserOp.set_choose) (.exactly 1)
  | .SET_IS_EMPTY => .spine (Term.UOp UserOp.set_is_empty) (.exactly 1)
  | .SET_IS_SINGLETON => .spine (Term.UOp UserOp.set_is_singleton) (.exactly 1)
  -- `:right-assoc` without a nil in `Cpc.eo`, but binary in cvc5 (its type rule
  -- takes two children), and Logos translates only the binary application.
  | .SET_INSERT => .spine (Term.UOp UserOp.set_insert) (.exactly 2)
  | .BITVECTOR_UBV_TO_INT => .spine (Term.UOp UserOp.ubv_to_int) (.exactly 1)
  | .BITVECTOR_SBV_TO_INT => .spine (Term.UOp UserOp.sbv_to_int) (.exactly 1)
  | .BITVECTOR_CONCAT => .rightAssocNil UserOp.concat .typed
  | .BITVECTOR_AND => .rightAssocNil UserOp.bvand .typed
  | .BITVECTOR_OR => .rightAssocNil UserOp.bvor .typed
  | .BITVECTOR_XOR => .rightAssocNil UserOp.bvxor .typed
  | .BITVECTOR_ADD => .rightAssocNil UserOp.bvadd .typed
  | .BITVECTOR_MULT => .rightAssocNil UserOp.bvmul .typed
  | .BITVECTOR_NOT => .spine (Term.UOp UserOp.bvnot) (.exactly 1)
  | .BITVECTOR_NEG => .spine (Term.UOp UserOp.bvneg) (.exactly 1)
  | .BITVECTOR_REDOR => .spine (Term.UOp UserOp.bvredor) (.exactly 1)
  | .BITVECTOR_REDAND => .spine (Term.UOp UserOp.bvredand) (.exactly 1)
  | .BITVECTOR_NEGO => .spine (Term.UOp UserOp.bvnego) (.exactly 1)
  | .BITVECTOR_SIZE => .spine (Term.UOp UserOp._at_bvsize) (.exactly 1)
  | .BITVECTOR_NAND => .spine (Term.UOp UserOp.bvnand) (.exactly 2)
  | .BITVECTOR_NOR => .spine (Term.UOp UserOp.bvnor) (.exactly 2)
  | .BITVECTOR_XNOR => .spine (Term.UOp UserOp.bvxnor) (.exactly 2)
  | .BITVECTOR_COMP => .spine (Term.UOp UserOp.bvcomp) (.exactly 2)
  | .BITVECTOR_SUB => .spine (Term.UOp UserOp.bvsub) (.exactly 2)
  | .BITVECTOR_UDIV => .spine (Term.UOp UserOp.bvudiv) (.exactly 2)
  | .BITVECTOR_UREM => .spine (Term.UOp UserOp.bvurem) (.exactly 2)
  | .BITVECTOR_SDIV => .spine (Term.UOp UserOp.bvsdiv) (.exactly 2)
  | .BITVECTOR_SREM => .spine (Term.UOp UserOp.bvsrem) (.exactly 2)
  | .BITVECTOR_SMOD => .spine (Term.UOp UserOp.bvsmod) (.exactly 2)
  | .BITVECTOR_SHL => .spine (Term.UOp UserOp.bvshl) (.exactly 2)
  | .BITVECTOR_LSHR => .spine (Term.UOp UserOp.bvlshr) (.exactly 2)
  | .BITVECTOR_ASHR => .spine (Term.UOp UserOp.bvashr) (.exactly 2)
  | .BITVECTOR_ULT => .spine (Term.UOp UserOp.bvult) (.exactly 2)
  | .BITVECTOR_ULE => .spine (Term.UOp UserOp.bvule) (.exactly 2)
  | .BITVECTOR_UGT => .spine (Term.UOp UserOp.bvugt) (.exactly 2)
  | .BITVECTOR_UGE => .spine (Term.UOp UserOp.bvuge) (.exactly 2)
  | .BITVECTOR_SLT => .spine (Term.UOp UserOp.bvslt) (.exactly 2)
  | .BITVECTOR_SLE => .spine (Term.UOp UserOp.bvsle) (.exactly 2)
  | .BITVECTOR_SGT => .spine (Term.UOp UserOp.bvsgt) (.exactly 2)
  | .BITVECTOR_SGE => .spine (Term.UOp UserOp.bvsge) (.exactly 2)
  | .BITVECTOR_ULTBV => .spine (Term.UOp UserOp.bvultbv) (.exactly 2)
  | .BITVECTOR_SLTBV => .spine (Term.UOp UserOp.bvsltbv) (.exactly 2)
  | .BITVECTOR_UADDO => .spine (Term.UOp UserOp.bvuaddo) (.exactly 2)
  | .BITVECTOR_SADDO => .spine (Term.UOp UserOp.bvsaddo) (.exactly 2)
  | .BITVECTOR_UMULO => .spine (Term.UOp UserOp.bvumulo) (.exactly 2)
  | .BITVECTOR_SMULO => .spine (Term.UOp UserOp.bvsmulo) (.exactly 2)
  | .BITVECTOR_USUBO => .spine (Term.UOp UserOp.bvusubo) (.exactly 2)
  | .BITVECTOR_SSUBO => .spine (Term.UOp UserOp.bvssubo) (.exactly 2)
  | .BITVECTOR_SDIVO => .spine (Term.UOp UserOp.bvsdivo) (.exactly 2)
  | .BITVECTOR_ITE => .spine (Term.UOp UserOp.bvite) (.exactly 3)
  | .BOUND_VAR_LIST => .binderList
  | .FORALL => .binder UserOp.forall
  | .EXISTS => .binder UserOp.exists
  | _ => .none

/-- The CPC form of each indexed operator. -/
def indexedEoShape : Kind → List Int → AppShape
  | .BITVECTOR_EXTRACT, [i, j] =>
      .spine (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) (.exactly 1)
  | .REGEXP_REPEAT, [i] => .spine (Term.UOp1 UserOp1.re_exp (Term.Numeral i)) (.exactly 1)
  | .REGEXP_LOOP, [i, j] =>
      .spine (Term.UOp2 UserOp2.re_loop (Term.Numeral i) (Term.Numeral j)) (.exactly 1)
  | .INT_TO_BITVECTOR, [i] => .spine (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (.exactly 1)
  | .BITVECTOR_REPEAT, [i] => .spine (Term.UOp1 UserOp1.repeat (Term.Numeral i)) (.exactly 1)
  | .BITVECTOR_ZERO_EXTEND, [i] => .spine (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) (.exactly 1)
  | .BITVECTOR_SIGN_EXTEND, [i] => .spine (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) (.exactly 1)
  | .BITVECTOR_ROTATE_LEFT, [i] => .spine (Term.UOp1 UserOp1.rotate_left (Term.Numeral i)) (.exactly 1)
  | .BITVECTOR_ROTATE_RIGHT, [i] => .spine (Term.UOp1 UserOp1.rotate_right (Term.Numeral i)) (.exactly 1)
  | _, _ => .none

/-- The CPC form of an operator that is a term, given its translation `f`. -/
def nodeEoShape : Kind → Term → AppShape
  | .APPLY_UF, f => .spine f (.atLeast 1)
  -- `f` is a constructor (`Term.DtCons`), applied to its fields; a nullary
  -- constructor is the constructor itself. Applications of the wrong arity
  -- are not well typed.
  | .APPLY_CONSTRUCTOR, f => .spine f (.atLeast 0)
  -- `f` is a selector (`Term.DtSel`).
  | .APPLY_SELECTOR, f => .spine f (.exactly 1)
  -- `((_ is C) t)`, with `f` the constructor `C`.
  | .APPLY_TESTER, f => .spine (Term.UOp1 UserOp1.is f) (.exactly 1)
  -- `((_ update s) t u)`, with `f` the selector `s`.
  | .APPLY_UPDATER, f => .spine (Term.UOp1 UserOp1.update f) (.exactly 2)
  | _, _ => .none

/-- The `:right-assoc-nil` bit-vector operators, whose nil is typed. -/
def _root_.Eo.UserOp.isBvNary (op : UserOp) : Bool :=
  op == UserOp.concat || op == UserOp.bvand || op == UserOp.bvor || op == UserOp.bvxor ||
    op == UserOp.bvadd || op == UserOp.bvmul

/-- The `:right-assoc-nil` operators with a typed nil whose congruence is proved
like that of the bit-vector ones: those and `str.++`. -/
def _root_.Eo.UserOp.isTypedNary (op : UserOp) : Bool :=
  op.isBvNary || op == UserOp.str_concat

/-- The `:right-assoc-nil` regular expression operators, whose nil is constant. -/
def _root_.Eo.UserOp.isReNary (op : UserOp) : Bool :=
  op == UserOp.re_concat || op == UserOp.re_inter || op == UserOp.re_union

/-- Shapes whose congruence is proven child by child: rewriting any child to an
equivalent node gives an equivalent application. Binders are handled separately,
since their variable list is not a term. Typed argument lists (`distinct`) are
not yet: their children are not rewritten. -/
def AppShape.isChildCongruent : AppShape → Bool
  | .spine _ _ => true
  | .rightAssocNil op (.const _) => op == UserOp.and || op == UserOp.or || op.isReNary
  | .rightAssocNil op .typed => op == UserOp.plus || op == UserOp.mult || op.isTypedNary
  | .none => true
  | .typedList _ | .binderList | .binder _ => false

/-- Translate an application of the given shape to its translated children. -/
def AppShape.toEo : AppShape → List Term → Term
  | .spine head arity, xs => if arity.accepts xs.length then xs.foldl Term.Apply head else Term.Stuck
  | .rightAssocNil op nil, xs =>
    if 2 ≤ xs.length then eoRightAssocNil op (nil.eval op (xs.headD Term.Stuck)) xs
    else Term.Stuck
  | .typedList op, xs =>
    if 2 ≤ xs.length then
      eoApp1 op (eoRightAssocNil UserOp._at__at_TypedList_cons
        (typedNil UserOp._at__at_TypedList_cons (xs.headD Term.Stuck)) xs)
    else Term.Stuck
  | .binderList, xs => eoList xs
  | .binder op, [vs, body] | .binder op, [vs, body, _] => eoApp2 op vs body
  | .binder _, _ => Term.Stuck
  | .none, _ => Term.Stuck

/-- The number of the declared constant `name` (`Term.UConst`): the code points of
the name as a numeral in bijective base `0x110000`, with digits `1` to
`0x110000`. Different names have different numbers, so constants are identified
by name, as in SMT-LIB. -/
def constId (name : String) : Nat :=
  name.toList.foldl (fun acc c => acc * 0x110000 + (c.toNat + 1)) 0

namespace Node

def toEo : Node → Term
  | .const c => c.toEo
  | .var name T => Term.UConst (constId name) T.toEo
  | .boundVar name T => Term.Var (Term.String (native_string_lit name)) T.toEo
  | .app (.kind k) cs => k.eoShape.toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)
  | .app (.indexed k is) cs =>
      (indexedEoShape k is.toList).toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)
  | .app (.node k f) cs =>
      (nodeEoShape k f.toEo).toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEo)

/-- The CPC shape of an application with operator `op`. -/
def _root_.Telos.Op.eoShape : Op → AppShape
  | .kind k => k.eoShape
  | .indexed k is => indexedEoShape k is.toList
  | .node k f => nodeEoShape k f.toEo

theorem toEo_app (op : Op) (cs : Array Node) :
    (Node.app op cs).toEo = op.eoShape.toEo (cs.toList.map Node.toEo) := by
  cases op <;> (rw [Node.toEo]; simp [Op.eoShape])

/-- The Logos SMT term of a node. -/
def toSmt (t : Node) : SmtTerm :=
  __eo_to_smt t.toEo

/-- The Logos SMT type of a node; `SmtType.None` when it is ill typed. -/
def smtType (t : Node) : SmtType :=
  __smtx_typeof t.toSmt

/-- A node is well typed when its translation has an SMT type. -/
def WellTyped (t : Node) : Prop :=
  t.smtType ≠ SmtType.None

instance (t : Node) : Decidable t.WellTyped :=
  inferInstanceAs (Decidable (_ ≠ _))

end Node

/-- The CPC formula `(= t s)`. -/
def eqFormula (t s : Node) : Term :=
  eoApp2 UserOp.eq t.toEo s.toEo

namespace Node

/-- cvc5's `getType()`: the type of a well-typed node, and `none` for an
ill-typed one. It is computed by Logos's type checker, so there is no second
type system to keep in sync. -/
def getType (t : Node) : Option TypeNode :=
  TypeNode.ofSmt t.smtType

theorem wellTyped_of_getType {t : Node} {T : TypeNode} (h : t.getType = some T) :
    t.WellTyped := by
  intro hNone
  simp [getType, hNone, TypeNode.ofSmt] at h

end Node

end Telos
