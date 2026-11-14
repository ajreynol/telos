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
  | .bitVector w v => s!"(_ bv{v} {w})"
  | .string s => "\"" ++ String.ofList (s.map Char.ofNat) ++ "\""

def Kind.smtLibName : Kind → String
  | .EQUAL => "=" | .NOT => "not" | .AND => "and" | .IMPLIES => "=>" | .OR => "or"
  | .XOR => "xor" | .ITE => "ite" | .FORALL => "forall" | .EXISTS => "exists"
  | .BITVECTOR_EXTRACT => "extract" | .DISTINCT => "distinct"
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
  | .app op cs =>
    let head := match op with
      | .kind k => k.smtLibName
      | .indexed k is => s!"(_ {k.smtLibName} {String.intercalate " " (is.toList.map toString)})"
      | .node _ f => f.toSmtLib
    "(" ++ String.intercalate " " (head :: cs.toList.map Node.toSmtLib) ++ ")"

instance : ToString Node := ⟨Node.toSmtLib⟩

end Telos
