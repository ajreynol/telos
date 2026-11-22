import Telos.Core.Node.Node

/-!
# Printing nodes in SMT-LIB syntax

For tests, debugging and differential testing against cvc5. Untrusted.
-/

namespace Telos

def TypeNode.toSmtLib : TypeNode → String
  | .boolean => "Bool"
  | .integer => "Int"
  | .real => "Real"
  | .string => "String"
  | .regExp => "RegLan"
  | .bitVector w => s!"(_ BitVec {w})"
  | .array i e => s!"(Array {i.toSmtLib} {e.toSmtLib})"
  | .sequence e => s!"(Seq {e.toSmtLib})"
  | .set e => s!"(Set {e.toSmtLib})"
  | .function a r => s!"(-> {a.toSmtLib} {r.toSmtLib})"
  | .sort i => s!"U{i}"
  | .datatype s _ | .typeRef s => s
  | .unitTuple => "UnitTuple"
  | .tuple h rest => s!"(Tuple {h.toSmtLib}{tail rest})"
where
  tail : TypeNode → String
    | .tuple h rest => s!" {h.toSmtLib}{tail rest}"
    | .unitTuple => ""
    | T => s!" {T.toSmtLib}"

def Const.toSmtLib : Const → String
  | .boolean b => if b then "true" else "false"
  -- Arithmetic literals as single tokens, as Eunoia writes them and as cvc5 prints
  -- them with `--print-arith-lit-token`: `-3`, `1/2`, `-5/2`, `3/1`.
  | .integer n => toString n
  | .rational q => s!"{q.num}/{q.den}"
  | .bitVector w v =>
    -- `#b…`, as cvc5 prints bit-vector constants.
    "#b" ++ String.ofList ((List.range w.toNat).reverse.map fun i => if v.toNat.testBit i then '1' else '0')
  | .string s => "\"" ++ String.ofList (s.map Char.ofNat) ++ "\""
  | .emptySet T => s!"(as set.empty {(TypeNode.set T).toSmtLib})"
  | .dtCons _ i => s!"<constructor {i}>"
  | .dtSel _ i j => s!"<selector {i} {j}>"

def Kind.smtLibName : Kind → String
  | .EQUAL => "=" | .NOT => "not" | .AND => "and" | .IMPLIES => "=>" | .OR => "or"
  | .XOR => "xor" | .ITE => "ite" | .FORALL => "forall" | .EXISTS => "exists"
  | .BITVECTOR_EXTRACT => "extract" | .DISTINCT => "distinct"
  | .BITVECTOR_CONCAT => "concat"
  | .BITVECTOR_AND => "bvand"
  | .BITVECTOR_OR => "bvor"
  | .BITVECTOR_XOR => "bvxor"
  | .BITVECTOR_ADD => "bvadd"
  | .BITVECTOR_MULT => "bvmul"
  | .BITVECTOR_NOT => "bvnot"
  | .BITVECTOR_NEG => "bvneg"
  | .BITVECTOR_REDOR => "bvredor"
  | .BITVECTOR_REDAND => "bvredand"
  | .BITVECTOR_NEGO => "bvnego"
  | .BITVECTOR_SIZE => "@bvsize"
  | .BITVECTOR_NAND => "bvnand"
  | .BITVECTOR_NOR => "bvnor"
  | .BITVECTOR_XNOR => "bvxnor"
  | .BITVECTOR_COMP => "bvcomp"
  | .BITVECTOR_SUB => "bvsub"
  | .BITVECTOR_UDIV => "bvudiv"
  | .BITVECTOR_UREM => "bvurem"
  | .BITVECTOR_SDIV => "bvsdiv"
  | .BITVECTOR_SREM => "bvsrem"
  | .BITVECTOR_SMOD => "bvsmod"
  | .BITVECTOR_SHL => "bvshl"
  | .BITVECTOR_LSHR => "bvlshr"
  | .BITVECTOR_ASHR => "bvashr"
  | .BITVECTOR_ULT => "bvult"
  | .BITVECTOR_ULE => "bvule"
  | .BITVECTOR_UGT => "bvugt"
  | .BITVECTOR_UGE => "bvuge"
  | .BITVECTOR_SLT => "bvslt"
  | .BITVECTOR_SLE => "bvsle"
  | .BITVECTOR_SGT => "bvsgt"
  | .BITVECTOR_SGE => "bvsge"
  | .BITVECTOR_ULTBV => "bvultbv"
  | .BITVECTOR_SLTBV => "bvsltbv"
  | .BITVECTOR_UADDO => "bvuaddo"
  | .BITVECTOR_SADDO => "bvsaddo"
  | .BITVECTOR_UMULO => "bvumulo"
  | .BITVECTOR_SMULO => "bvsmulo"
  | .BITVECTOR_USUBO => "bvusubo"
  | .BITVECTOR_SSUBO => "bvssubo"
  | .BITVECTOR_SDIVO => "bvsdivo"
  | .BITVECTOR_ITE => "bvite"
  | .SELECT => "select" | .STORE => "store"
  | .SET_SINGLETON => "set.singleton" | .SET_UNION => "set.union" | .SET_INTER => "set.inter"
  | .SET_MINUS => "set.minus" | .SET_MEMBER => "set.member" | .SET_SUBSET => "set.subset"
  | .SET_CHOOSE => "set.choose" | .SET_IS_EMPTY => "set.is_empty"
  | .SET_IS_SINGLETON => "set.is_singleton" | .SET_INSERT => "set.insert"
  | .STRING_CONCAT => "str.++"
  | .REGEXP_CONCAT => "re.++"
  | .REGEXP_INTER => "re.inter"
  | .REGEXP_UNION => "re.union"
  | .STRING_LENGTH => "str.len"
  | .STRING_SUBSTR => "str.substr"
  | .STRING_UPDATE => "str.update"
  | .STRING_CHARAT => "str.at"
  | .STRING_CONTAINS => "str.contains"
  | .STRING_LT => "str.<"
  | .STRING_LEQ => "str.<="
  | .STRING_INDEXOF => "str.indexof"
  | .STRING_INDEXOF_RE => "str.indexof_re"
  | .STRING_REPLACE => "str.replace"
  | .STRING_REPLACE_ALL => "str.replace_all"
  | .STRING_REPLACE_RE => "str.replace_re"
  | .STRING_REPLACE_RE_ALL => "str.replace_re_all"
  | .STRING_PREFIX => "str.prefixof"
  | .STRING_SUFFIX => "str.suffixof"
  | .STRING_IS_DIGIT => "str.is_digit"
  | .STRING_ITOS => "str.from_int"
  | .STRING_STOI => "str.to_int"
  | .STRING_TO_CODE => "str.to_code"
  | .STRING_FROM_CODE => "str.from_code"
  | .STRING_TO_LOWER => "str.to_lower"
  | .STRING_TO_UPPER => "str.to_upper"
  | .STRING_REV => "str.rev"
  | .STRING_TO_REGEXP => "str.to_re"
  | .STRING_IN_REGEXP => "str.in_re"
  | .REGEXP_NONE => "re.none"
  | .REGEXP_ALL => "re.all"
  | .REGEXP_ALLCHAR => "re.allchar"
  | .REGEXP_DIFF => "re.diff"
  | .REGEXP_STAR => "re.*"
  | .REGEXP_PLUS => "re.+"
  | .REGEXP_OPT => "re.opt"
  | .REGEXP_RANGE => "re.range"
  | .REGEXP_COMPLEMENT => "re.comp"
  | .REGEXP_REPEAT => "re.^"
  | .REGEXP_LOOP => "re.loop"
  | .POW2 => "int.pow2" | .INTS_LOG2 => "int.log2" | .INTS_ISPOW2 => "int.ispow2"
  | .INT_TO_BITVECTOR => "int_to_bv"
  | .BITVECTOR_UBV_TO_INT => "ubv_to_int"
  | .BITVECTOR_SBV_TO_INT => "sbv_to_int"
  | .BITVECTOR_REPEAT => "repeat"
  | .BITVECTOR_ZERO_EXTEND => "zero_extend"
  | .BITVECTOR_SIGN_EXTEND => "sign_extend"
  | .BITVECTOR_ROTATE_LEFT => "rotate_left"
  | .BITVECTOR_ROTATE_RIGHT => "rotate_right"
  | .ADD => "+" | .SUB => "-" | .NEG => "-" | .MULT => "*" | .DIVISION => "/"
  | .INTS_DIVISION => "div" | .INTS_MODULUS => "mod" | .ABS => "abs"
  | .DIVISION_TOTAL => "/_total" | .INTS_DIVISION_TOTAL => "div_total"
  | .INTS_MODULUS_TOTAL => "mod_total"
  | .LT => "<" | .LEQ => "<=" | .GT => ">" | .GEQ => ">="
  | .TO_REAL => "to_real" | .TO_INTEGER => "to_int" | .IS_INTEGER => "is_int"
  | .TUPLE => "tuple" | .TUPLE_UNIT => "tuple.unit" | .TUPLE_SELECT => "tuple.select"
  | .TUPLE_UPDATE => "tuple.update"
  | k => toString (repr k)

/-- A field type of a parametric datatype as declared: a parameter, or a sort
applied to field types. -/
inductive TypeTemplate where
  | param (k : Nat)
  | app (head : String) (args : List TypeTemplate)
  deriving Inhabited

/-- The names of datatype constructors and selectors, which `TypeNode` does not
record (as in Logos): by datatype name and position. The front end fills it from
the script's `declare-datatypes`. -/
structure DtNames where
  cons : String → Nat → Option String := fun _ _ => none
  sel : String → Nat → Nat → Option String := fun _ _ _ => none
  /-- The names of uninterpreted sorts, which Logos numbers. -/
  sort : Nat → Option String := fun _ => none
  /-- For a parametric datatype, by name: its number of parameters, and the
  field types of its constructors as declared, over the parameters. -/
  template : String → Option (Nat × List (List TypeTemplate)) := fun _ => none

/-- The datatype `D` that a Logos instance name `.par_k_D` instantiates (Logos's
parser names the instances of parametric datatypes so). -/
def parInstanceOf (s : String) : Option String :=
  match s.toList with
  | '.' :: 'p' :: 'a' :: 'r' :: '_' :: rest =>
    let digits := rest.takeWhile Char.isDigit
    match rest.drop digits.length with
    | '_' :: d => if digits.isEmpty then none else some (String.ofList d)
    | _ => none
  | _ => none

/-- The source name of a datatype, for an instance its parametric datatype's. -/
def DtNames.baseName (s : String) : String := (parInstanceOf s).getD s

/-- The parameters of an instance of a parametric datatype, found by matching
the instance's field types with the declared ones (`fuel` bounds the instances
of other datatypes looked into). A parameter that no field uses is not found. -/
partial def DtNames.instArgs (N : DtNames) (fuel : Nat) (T : TypeNode) : Option (List TypeNode) := do
  let .datatype s _ := T | none
  let d ← parInstanceOf s
  let (arity, cons) ← N.template d
  let mut σ : Array (Option TypeNode) := Array.replicate arity none
  for (fts, i) in cons.zipIdx do
    let fs ← T.dtFields? i
    for (tt, F) in fts.zip fs do
      σ := unify fuel T σ tt F
  σ.toList.mapM id
where
  unify (fuel : Nat) (self : TypeNode) (σ : Array (Option TypeNode)) :
      TypeTemplate → TypeNode → Array (Option TypeNode)
    | .param k, F => if (σ[k]?).join.isNone && k < σ.size then σ.set! k (some F) else σ
    | .app h args, F =>
      let sub : Option (List TypeNode) := match h, F with
        | "Array", .array i e => some [i, e]
        | "Set", .set e => some [e]
        | "Seq", .sequence e => some [e]
        | "Tuple", F => F.tupleFields?
        | h, F@(.datatype s' _) =>
          if F == self || fuel == 0 || parInstanceOf s' != some h then none
          else N.instArgs (fuel - 1) F
        | _, _ => none
      match sub with
      | some Fs => (args.zip Fs).foldl (fun σ (a, F) => unify fuel self σ a F) σ
      | none => σ

/-- A type in SMT-LIB syntax, with `N` naming uninterpreted sorts and the
instances of parametric datatypes. -/
partial def TypeNode.toSmtLibWith (N : DtNames) : TypeNode → String
  | .sort i => (N.sort i).getD s!"U{i}"
  | .array i e => s!"(Array {i.toSmtLibWith N} {e.toSmtLibWith N})"
  | .sequence e => s!"(Seq {e.toSmtLibWith N})"
  | .set e => s!"(Set {e.toSmtLibWith N})"
  | .function a r => s!"(-> {a.toSmtLibWith N} {r.toSmtLibWith N})"
  | T@(.datatype s _) =>
    match parInstanceOf s with
    | some d =>
      match N.instArgs 8 T with
      | some [] | none => d
      | some as => "(" ++ String.intercalate " " (d :: as.map (·.toSmtLibWith N)) ++ ")"
    | none => s
  | .typeRef s => DtNames.baseName s
  | T@(.tuple ..) =>
    match T.tupleFields? with
    | some fs => "(" ++ String.intercalate " " ("Tuple" :: fs.map (·.toSmtLibWith N)) ++ ")"
    | none => T.toSmtLib
  | T => T.toSmtLib

/-- Whether a datatype is an instance of a parametric datatype with parameters,
whose constructors cvc5 prints with their type, `(as C T)`. -/
def DtNames.isParametric (N : DtNames) : TypeNode → Bool
  | .datatype s _ => match parInstanceOf s >>= N.template with
    | some (arity, _) => arity > 0
    | none => false
  | _ => false

def DtNames.consName (N : DtNames) : TypeNode → Nat → String
  | .datatype s _, i => (N.cons (DtNames.baseName s) i).getD s!"{s}.c{i}"
  | _, i => s!"?.c{i}"

def DtNames.selName (N : DtNames) : TypeNode → Nat → Nat → String
  | .datatype s _, i, j => (N.sel (DtNames.baseName s) i j).getD s!"{s}.c{i}.s{j}"
  | _, i, j => s!"?.c{i}.s{j}"

/-- The top of a node in SMT-LIB syntax, with `N` naming constructors and
selectors, and `pc` printing its subterms (`toSmtLibWith`, or the let printer's
names for shared subterms). -/
def Node.toSmtLibTop (N : DtNames) (pc : Node → String) : Node → String
  -- the operator of a tester in the equality engine (cvc5's `is_C`)
  | .app (.kind .APPLY_TESTER) #[.const (.dtCons T i)] => s!"is_{N.consName T i}"
  | .const (.dtCons T i) =>
    if N.isParametric T then s!"(as {N.consName T i} {T.toSmtLibWith N})" else N.consName T i
  -- `(tuple a₁ … aₙ)`, from `(TUPLE a₁ (… (TUPLE aₙ TUPLE_UNIT)))`
  | n@(.app (.kind .TUPLE) #[_, _]) =>
    let rec elems (fuel : Nat) : Node → List Node × Option Node
      | .app (.kind .TUPLE) #[a, r] =>
        if fuel == 0 then ([], some r) else
        let (es, tl) := elems (fuel - 1) r
        (a :: es, tl)
      | .app (.kind .TUPLE_UNIT) #[] => ([], none)
      | r => ([], some r)
    let (es, tl) := elems 100000 n
    let parts := es.map pc ++ (tl.map pc).toList
    "(" ++ String.intercalate " " ("tuple" :: parts) ++ ")"
  | .const (.dtSel T i j) => N.selName T i j
  | .const (.emptySet T) => s!"(as set.empty {(TypeNode.set T).toSmtLibWith N})"
  | .const c => c.toSmtLib
  | .var n _ | .boundVar n _ => n
  | .skolem id #[] => id.name
  | .skolem id cs =>
    "(" ++ String.intercalate " " (id.name :: cs.toList.map pc) ++ ")"
  | .app (.node .APPLY_CONSTRUCTOR f) #[] => pc f
  | .app (.node .APPLY_TESTER f) cs =>
    -- the constructor's name, without the type of a parametric datatype's
    let c := match f with
      | .const (.dtCons T i) => N.consName T i
      | f => pc f
    "(" ++ String.intercalate " " (s!"(_ is {c})" :: cs.toList.map pc) ++ ")"
  | .app (.node .APPLY_UPDATER f) cs =>
    "(" ++ String.intercalate " " (s!"(_ update {pc f})" :: cs.toList.map pc) ++ ")"
  | .app (.kind .BOUND_VAR_LIST) vs =>
    "(" ++ String.intercalate " " (vs.toList.map fun
      | .boundVar n T => s!"({n} {T.toSmtLibWith N})"
      | v => pc v) ++ ")"
  | .app (.kind k) #[] => k.smtLibName
  | .app op cs =>
    let head := match op with
      | .kind k => k.smtLibName
      | .indexed k is => s!"(_ {k.smtLibName} {String.intercalate " " (is.toList.map toString)})"
      | .node _ f => pc f
    "(" ++ String.intercalate " " (head :: cs.toList.map pc) ++ ")"

/-- A node in SMT-LIB syntax, with `N` naming constructors and selectors. -/
partial def Node.toSmtLibWith (N : DtNames) (n : Node) : String :=
  n.toSmtLibTop N (Node.toSmtLibWith N)

/-- A node in SMT-LIB syntax, with placeholder names for datatype constructors and
selectors. -/
def Node.toSmtLib (n : Node) : String := n.toSmtLibWith {}

instance : ToString Node := ⟨Node.toSmtLib⟩

end Telos
