import Telos.Node.Node

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
  | k => toString (repr k)

partial def Node.toSmtLib : Node → String
  | .const c => c.toSmtLib
  | .var n _ | .boundVar n _ => n
  | .app (.kind .BOUND_VAR_LIST) vs =>
    "(" ++ String.intercalate " " (vs.toList.map fun
      | .boundVar n T => s!"({n} {T.toSmtLib})"
      | v => v.toSmtLib) ++ ")"
  | .app (.kind k) #[] => k.smtLibName
  | .app op cs =>
    let head := match op with
      | .kind k => k.smtLibName
      | .indexed k is => s!"(_ {k.smtLibName} {String.intercalate " " (is.toList.map toString)})"
      | .node _ f => f.toSmtLib
    "(" ++ String.intercalate " " (head :: cs.toList.map Node.toSmtLib) ++ ")"

instance : ToString Node := ⟨Node.toSmtLib⟩

end Telos
