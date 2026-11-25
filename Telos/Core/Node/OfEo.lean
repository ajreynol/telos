import Telos.Core.Node.ToEo
import Telos.Core.Node.SmtTypeFast

/-!
# From Logos terms back to nodes

`Node.ofEo` is a partial inverse of `Node.toEo`. It reads the right-hand side of a
CPC rule's conclusion back as a node.

It is **not** part of the specification and needs no proof. Every use is checked:
a rewrite step only accepts `m := ofEo r` after checking that `m.toEo = r`
(`Telos/Core/Certified.lean`). So a gap here (a term it cannot read back)
only means that a rewrite does not apply.

Variables are read back as the matching variable of the node being rewritten,
when there is one, which keeps bound variables bound. Otherwise they become free
variables.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- A string of Logos, as a Lean string. -/
def nativeStr (s : native_String) : String := String.ofList (s.map Char.ofNat)

namespace TypeNode

mutual

/-- The inverse of `TypeNode.toEo`. -/
def ofEo : Term → Option TypeNode
  | .Bool => some .boolean
  | .UOp UserOp.Int => some .integer
  | .UOp UserOp.Real => some .real
  | .UOp UserOp.RegLan => some .regExp
  | .Apply (.UOp UserOp.Seq) (.UOp UserOp.Char) => some .string
  | .Apply (.UOp UserOp.BitVec) (.Numeral w) => some (.bitVector w)
  | .Apply (.Apply (.UOp UserOp.Array) i) e => .array <$> ofEo i <*> ofEo e
  | .Apply (.UOp UserOp.Seq) e => .sequence <$> ofEo e
  | .Apply (.UOp UserOp.Set) e => .set <$> ofEo e
  | .Apply (.Apply .FunType a) r => .function <$> ofEo a <*> ofEo r
  | .USort i => some (.sort i)
  | .DatatypeType s d => .datatype (nativeStr s) <$> dtDeclOfEo d
  | .DatatypeTypeRef s => some (.typeRef (nativeStr s))
  | .UOp UserOp.UnitTuple => some .unitTuple
  | .Apply (.Apply (.UOp UserOp.Tuple) h) rest => .tuple <$> ofEo h <*> ofEo rest
  | _ => none

def dtDeclOfEo : DatatypeDecl → Option DtDecl
  | .nil => some .nil
  | .cons s d rest => .cons (nativeStr s) <$> dtOfEo d <*> dtDeclOfEo rest

def dtOfEo : Datatype → Option Dt
  | .null => some .null
  | .sum c rest => .sum <$> dtConsOfEo c <*> dtOfEo rest

def dtConsOfEo : DatatypeCons → Option DtCons
  | .unit => some .unit
  | .cons f rest => .cons <$> ofEo f <*> dtConsOfEo rest

end

end TypeNode

namespace Const

/-- The inverse of `Const.toEo`. -/
def ofEo : Term → Option Const
  | .Boolean b => some (.boolean b)
  | .Numeral n => some (.integer n)
  | .Rational q => some (.rational q)
  | .Binary w v => some (.bitVector w v)
  | .String s => some (.string s)
  | .UOp1 UserOp1.seq_empty (.Apply (.UOp UserOp.Seq) T) =>
    if T == .UOp UserOp.Char then some (.string []) else .emptySeq <$> TypeNode.ofEo T
  | .UOp1 UserOp1.set_empty (.Apply (.UOp UserOp.Set) T) => .emptySet <$> TypeNode.ofEo T
  | _ => none

end Const

/-- The head and arguments of an application spine `(… ((h x₁) x₂) … xₙ)`. -/
def eoSpine : Term → Term × List Term
  | .Apply f x => let (h, xs) := eoSpine f; (h, xs ++ [x])
  | t => (t, [])

/-- The elements of `(op x₁ (op x₂ … (op xₙ nil)))`. -/
def eoRightAssocNilElems (op : UserOp) (nil : Term) : Term → Option (List Term)
  | .Apply (.Apply (.UOp o) x) rest =>
      if o == op then (x :: ·) <$> eoRightAssocNilElems op nil rest else none
  | t => if t == nil then some [] else none

/-- The elements of an Eunoia list `(@list x₁ … xₙ)`. -/
def eoListElems : Term → Option (List Term)
  | .Apply (.Apply .__eo_List_cons x) rest => (x :: ·) <$> eoListElems rest
  | .__eo_List_nil => some []
  | _ => none

/-- A string literal of Logos, as a Lean string. -/
def nativeStringToString (s : native_String) : String :=
  String.ofList (s.map Char.ofNat)

/-- The `:right-assoc-nil` kind of an operator, for the bit-vector operators
(the others are read back explicitly in `ofEo`). -/
def naryKindOf : UserOp → Option Kind
  | UserOp.concat => some .BITVECTOR_CONCAT
  | UserOp.str_concat => some .STRING_CONCAT
  | UserOp.re_concat => some .REGEXP_CONCAT
  | UserOp.re_inter => some .REGEXP_INTER
  | UserOp.re_union => some .REGEXP_UNION
  | UserOp.bvand => some .BITVECTOR_AND
  | UserOp.bvor => some .BITVECTOR_OR
  | UserOp.bvxor => some .BITVECTOR_XOR
  | UserOp.bvadd => some .BITVECTOR_ADD
  | UserOp.bvmul => some .BITVECTOR_MULT
  | _ => none

/-- The kind of an operator with one index. -/
def indexedKindOf : UserOp1 → Option Kind
  | UserOp1.re_exp => some .REGEXP_REPEAT
  | UserOp1.int_to_bv => some .INT_TO_BITVECTOR
  | UserOp1.repeat => some .BITVECTOR_REPEAT
  | UserOp1.zero_extend => some .BITVECTOR_ZERO_EXTEND
  | UserOp1.sign_extend => some .BITVECTOR_SIGN_EXTEND
  | UserOp1.rotate_left => some .BITVECTOR_ROTATE_LEFT
  | UserOp1.rotate_right => some .BITVECTOR_ROTATE_RIGHT
  | UserOp1.tuple_select => some .TUPLE_SELECT
  | _ => none

/-- Kinds read back from their spine shape (`Kind.eoShape`). -/
def shapeKinds : List Kind := [.TUPLE, .TUPLE_UNIT, .STRING_LENGTH, .STRING_SUBSTR, .STRING_UPDATE, .STRING_CHARAT, .STRING_CONTAINS, .STRING_LT, .STRING_LEQ, .STRING_INDEXOF, .STRING_INDEXOF_RE, .STRING_REPLACE, .STRING_REPLACE_ALL, .STRING_REPLACE_RE, .STRING_REPLACE_RE_ALL, .STRING_PREFIX, .STRING_SUFFIX, .STRING_IS_DIGIT, .STRING_ITOS, .STRING_STOI, .STRING_TO_CODE, .STRING_FROM_CODE, .STRING_TO_LOWER, .STRING_TO_UPPER, .STRING_REV, .SEQ_UNIT, .SEQ_NTH, .STRING_TO_REGEXP, .STRING_IN_REGEXP, .REGEXP_NONE, .REGEXP_ALL, .REGEXP_ALLCHAR, .REGEXP_DIFF, .REGEXP_STAR, .REGEXP_PLUS, .REGEXP_OPT, .REGEXP_RANGE, .REGEXP_COMPLEMENT, .SELECT, .STORE, .SET_SINGLETON, .SET_UNION, .SET_INTER, .SET_MINUS, .SET_MEMBER, .SET_SUBSET, .SET_CHOOSE, .SET_IS_EMPTY, .SET_IS_SINGLETON, .SET_INSERT, .POW2, .INTS_LOG2, .INTS_ISPOW2, .BITVECTOR_UBV_TO_INT, .BITVECTOR_SBV_TO_INT, .BITVECTOR_NOT, .BITVECTOR_NEG, .BITVECTOR_REDOR, .BITVECTOR_REDAND, .BITVECTOR_NEGO, .BITVECTOR_SIZE, .BITVECTOR_NAND, .BITVECTOR_NOR, .BITVECTOR_XNOR, .BITVECTOR_COMP, .BITVECTOR_SUB, .BITVECTOR_UDIV, .BITVECTOR_UREM, .BITVECTOR_SDIV, .BITVECTOR_SREM, .BITVECTOR_SMOD, .BITVECTOR_SHL, .BITVECTOR_LSHR, .BITVECTOR_ASHR, .BITVECTOR_ULT, .BITVECTOR_ULE, .BITVECTOR_UGT, .BITVECTOR_UGE, .BITVECTOR_SLT, .BITVECTOR_SLE, .BITVECTOR_SGT, .BITVECTOR_SGE, .BITVECTOR_ULTBV, .BITVECTOR_SLTBV, .BITVECTOR_UADDO, .BITVECTOR_SADDO, .BITVECTOR_UMULO, .BITVECTOR_SMULO, .BITVECTOR_USUBO, .BITVECTOR_SSUBO, .BITVECTOR_SDIVO, .BITVECTOR_ITE]

/-- The head operator of a skolem's CPC term (`SkolemId.eoShape`). -/
def skolemHead? (id : SkolemId) : Option UserOp :=
  match id.eoShape with
  | .spine (.UOp op) _ => some op
  | _ => none

namespace Node

/-- The variables (free and bound) and skolems occurring in a node. A skolem's
cache values are included: its meaning depends on them. -/
partial def vars : Node → List Node
  | n@(.var ..) | n@(.boundVar ..) => [n]
  | n@(.skolem _ cs) => n :: cs.toList.flatMap vars
  | .const _ => []
  | .app op cs =>
      let opVars := match op with
        | .node _ f => f.vars
        | _ => []
      opVars ++ cs.toList.flatMap vars

/-- The name of the declared constant numbered `n` (the inverse of `constId`). -/
partial def constName (n : Nat) : String :=
  go n []
where
  go (n : Nat) (acc : List Char) : String :=
    if n == 0 then String.ofList acc
    else
      let d := (n - 1) % 0x110000 + 1
      go ((n - d) / 0x110000) (Char.ofNat (d - 1) :: acc)

/-- The node a Logos variable stands for: the variable of `env` with this
translation, or a free variable. -/
def varOfEo (env : List (Term × Node)) (t : Term) (bound : Bool) : Option Node :=
  match env.find? (·.1 == t) with
  | some (_, v) => some v
  | none =>
    match t with
    | .Var (.String s) T =>
      (if bound then Node.boundVar else Node.var) (nativeStringToString s) <$> TypeNode.ofEo T
    | _ => none

/-- `ofEo`, with the translation of each variable of the environment. -/
partial def ofEoIn (env : List (Term × Node)) (t : Term) : Option Node := do
  -- A nullary constructor is an `APPLY_CONSTRUCTOR` application, as in cvc5,
  -- not the constructor symbol.
  if let .DtCons s d i := t then return ← dtApp .APPLY_CONSTRUCTOR (← dtCons s d i) []
  if let some c := Const.ofEo t then return .const c
  if let .Var .. := t then return ← varOfEo env t false
  if let .UConst i T := t then return .var (constName i) (← TypeNode.ofEo T)
  let (h, xs) := eoSpine t
  if let .UOp op := h then
    if let some id := SkolemId.all.find? (skolemHead? · == some op) then
      return ← skolemApp id xs
  match h, xs with
  | .UOp UserOp.and, [x, _] => nary .AND x
  | .UOp UserOp.or, [x, _] => nary .OR x
  | .UOp UserOp.plus, [x, _] => nary .ADD x
  | .UOp UserOp.mult, [x, _] => nary .MULT x
  | .UOp UserOp.neg, [_, _] => app .SUB xs
  | .UOp UserOp.__eoo_neg_2, [_] => app .NEG xs
  | .UOp UserOp.qdiv, [_, _] => app .DIVISION xs
  | .UOp UserOp.div, [_, _] => app .INTS_DIVISION xs
  | .UOp UserOp.mod, [_, _] => app .INTS_MODULUS xs
  | .UOp UserOp.qdiv_total, [_, _] => app .DIVISION_TOTAL xs
  | .UOp UserOp.div_total, [_, _] => app .INTS_DIVISION_TOTAL xs
  | .UOp UserOp.mod_total, [_, _] => app .INTS_MODULUS_TOTAL xs
  | .UOp UserOp.abs, [_] => app .ABS xs
  | .UOp UserOp.lt, [_, _] => app .LT xs
  | .UOp UserOp.leq, [_, _] => app .LEQ xs
  | .UOp UserOp.gt, [_, _] => app .GT xs
  | .UOp UserOp.geq, [_, _] => app .GEQ xs
  | .UOp UserOp.to_real, [_] => app .TO_REAL xs
  | .UOp UserOp.to_int, [_] => app .TO_INTEGER xs
  | .UOp UserOp.is_int, [_] => app .IS_INTEGER xs
  | .UOp UserOp.divisible, [_, _] => app .DIVISIBLE xs
  | .UOp UserOp.eq, [_, _] => app .EQUAL xs
  | .UOp UserOp.not, [_] => app .NOT xs
  | .UOp UserOp.imp, [_, _] => app .IMPLIES xs
  | .UOp UserOp.xor, [_, _] => app .XOR xs
  | .UOp UserOp.ite, [_, _, _] => app .ITE xs
  | .UOp UserOp.distinct, [l@(.Apply (.Apply _ first) _)] => do
    let cons := UserOp._at__at_TypedList_cons
    let elems ← eoRightAssocNilElems cons (typedNil cons first) l
    if elems.length < 2 then none
    app .DISTINCT elems
  | .UOp UserOp.forall, [vs, body] => binder .FORALL vs body
  | .UOp UserOp.exists, [vs, body] => binder .EXISTS vs body
  | .UOp3 UserOp3._at_re_unfold_pos_component s r i, [] =>
      return .skolem .RE_UNFOLD_POS_COMPONENT #[← ofEoIn env s, ← ofEoIn env r, ← ofEoIn env i]
  | .UOp2 UserOp2._at_quantifiers_skolemize q i, [] =>
      return .skolem .QUANTIFIERS_SKOLEMIZE #[← ofEoIn env q, ← ofEoIn env i]
  | .UOp2 UserOp2.re_loop (.Numeral i) (.Numeral j), [x] =>
      return .app (.indexed .REGEXP_LOOP #[i, j]) #[← ofEoIn env x]
  | .UOp2 UserOp2.extract (.Numeral i) (.Numeral j), [x] =>
      return .app (.indexed .BITVECTOR_EXTRACT #[i, j]) #[← ofEoIn env x]
  | .DtCons s d i, _ => dtApp .APPLY_CONSTRUCTOR (← dtCons s d i) xs
  | .DtSel s d i j, [_] => dtApp .APPLY_SELECTOR (← dtSel s d i j) xs
  | .UOp1 UserOp1.is (.DtCons s d i), [_] => dtApp .APPLY_TESTER (← dtCons s d i) xs
  | .UOp1 UserOp1.update (.DtSel s d i j), [_, _] => dtApp .APPLY_UPDATER (← dtSel s d i j) xs
  | .UOp1 op (.Numeral i), [x] =>
    match indexedKindOf op with
    | some k => return .app (.indexed k #[i]) #[← ofEoIn env x]
    | none => none
  | .UOp1 UserOp1.tuple_update (.Numeral i), [x, y] =>
    return .app (.indexed .TUPLE_UPDATE #[i]) #[← ofEoIn env x, ← ofEoIn env y]
  | .UOp op, [x, _] =>
    match naryKindOf op with
    | some k => nary k x
    | none => byShape op xs
  | .UOp op, _ => byShape op xs
  | f@(.Var ..), _ :: _ =>
      return .app (.node .APPLY_UF (← varOfEo env f false)) (← xs.mapM (ofEoIn env)).toArray
  | .UConst i T, _ :: _ =>
      return .app (.node .APPLY_UF (.var (constName i) (← TypeNode.ofEo T))) (← xs.mapM (ofEoIn env)).toArray
  | _, _ => none
where
  /-- The skolem `id` applied to `xs`: its cache values first, then (for a
  function skolem) the arguments of an `APPLY_UF`. -/
  skolemApp (id : SkolemId) (xs : List Term) : Option Node := do
    let n := id.numCacheVals
    if xs.length < n then none
    let k := Node.skolem id (← (xs.take n).mapM (ofEoIn env)).toArray
    match xs.drop n with
    | [] => return k
    | args => return .app (.node .APPLY_UF k) (← args.mapM (ofEoIn env)).toArray
  app (k : Kind) (xs : List Term) : Option Node := do
    return .app (.kind k) (← xs.mapM (ofEoIn env)).toArray
  dtCons (s : native_String) (d : DatatypeDecl) (i : Nat) : Option Node := do
    return .const (.dtCons (.datatype (nativeStr s) (← TypeNode.dtDeclOfEo d)) i)
  dtSel (s : native_String) (d : DatatypeDecl) (i j : Nat) : Option Node := do
    return .const (.dtSel (.datatype (nativeStr s) (← TypeNode.dtDeclOfEo d)) i j)
  dtApp (k : Kind) (f : Node) (xs : List Term) : Option Node := do
    return .app (.node k f) (← xs.mapM (ofEoIn env)).toArray
  nary (k : Kind) (first : Term) : Option Node := do
    let .rightAssocNil op nil := k.eoShape | none
    let elems ← eoRightAssocNilElems op (nil.eval op first) t
    if elems.length < 2 then none
    app k elems
  /-- A kind of `shapeKinds` whose shape is a spine with head `op` taking
  `xs.length` arguments. -/
  byShape (op : UserOp) (xs : List Term) : Option Node := do
    let k ← shapeKinds.find? fun k => match k.eoShape with
      | .spine (.UOp op') ar => op' == op && ar.accepts xs.length
      | _ => false
    app k xs
  binder (k : Kind) (vs body : Term) : Option Node := do
    let bvs ← (← eoListElems vs).mapM (varOfEo env · true)
    -- The body is read with the bound variables in scope, so that their
    -- occurrences are the same `boundVar`s.
    return .app (.kind k) #[.app (.kind .BOUND_VAR_LIST) bvs.toArray, ← ofEoIn (bvs.map (fun v => (v.toEo, v)) ++ env) body]

/-- A partial inverse of `toEo`, for the kinds `toEo` translates. Variables are
looked up in `env` first (see the module doc). -/
def ofEo (env : List Node) (t : Term) : Option Node :=
  ofEoIn (env.map fun v => (v.toEo, v)) t

end Node

end Telos
