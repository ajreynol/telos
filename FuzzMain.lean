import Telos

/-!
# `telos-fuzz`: random terms and their rewrites

`telos-fuzz SEED COUNT DEPTH [arith|uf|bv|arrays|mixed|strings|sets|datatypes|quantifiers] [--profile]` prints `COUNT` random Boolean terms over
`a`, `b`, `c` (and the integer `x`), each with its telos rewrite, as
`input<TAB>output` lines. With `arith`, the terms also contain comparisons of
integer and real terms over `x`, `y`, `r` and `s`. With `uf`, they also contain
equalities and `distinct` of terms of an uninterpreted sort `U` over `u`, `v`,
`w` and `f`, and `distinct` of Booleans and integers. With `bv`, they also
contain comparisons of terms of sort `(_ BitVec 4)` over `bx`, `by` and `bz`.
`scripts/fuzz.py` compares them against cvc5's rewriter. With `--profile`, a table
of where the rewriting time went is printed to standard error
(`Telos/Core/Profile.lean`); `scripts/profile.sh` runs a standard benchmark.
-/

open Telos Telos.Node

/-- A small linear congruential generator. -/
structure Rng where
  state : UInt64

def Rng.next (r : Rng) : Nat × Rng :=
  let s := r.state * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

abbrev GenM := StateM Rng

def pick (n : Nat) : GenM Nat := do
  let (v, r) := (← get).next
  set r
  return v % n

def atoms : Array Node :=
  #[.var "a" .boolean, .var "b" .boolean, .var "c" .boolean, mkTrue, mkFalse,
    eqNode (.var "x" .integer) (.const (.integer 0)),
    eqNode (.var "x" .integer) (.const (.integer 1))]

def intAtoms : Array Node :=
  #[.var "x" .integer, .var "y" .integer, .const (.integer 0), .const (.integer 1),
    .const (.integer 2), .const (.integer (-3))]

def realAtoms : Array Node :=
  #[.var "r" .real, .var "s" .real, .const (.rational 0), .const (.rational (mkRat 1 2)),
    .const (.rational 3)]

/-- A random arithmetic term, of type `Real` when `real`. -/
partial def genArith (real : Bool) : Nat → GenM Node
  | 0 => do
    if real && (← pick 3) == 0 then return mkNode .TO_REAL #[intAtoms[← pick intAtoms.size]!]
    let as := if real then realAtoms else intAtoms
    return as[← pick as.size]!
  | d + 1 => do
    match ← pick 11 with
    | 0 | 1 => genArith real 0
    | 2 => return mkNode .ADD (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genArith real d)
    | 3 => return mkNode .SUB #[← genArith real d, ← genArith real d]
    | 4 => return mkNode .NEG #[← genArith real d]
    | 5 => return mkNode .MULT #[← genArith real 0, ← genArith real d]
    | 6 => if real then return mkNode .TO_REAL #[← genArith false d] else genArith real d
    | 7 => return mkNode .MULT #[← genArith real d, ← genArith real d]
    | 8 => return mkNode .ABS #[← genArith real d]
    | 9 =>
      if real then return mkNode .DIVISION #[← genArith real d, (← genArith real 0)]
      else return mkNode .TO_INTEGER #[← genArith true d]
    | _ =>
      if real then genArith real d
      else
        let k := if (← pick 2) == 0 then Kind.INTS_DIVISION else .INTS_MODULUS
        return mkNode k #[← genArith false d, ← genArith false 0]

/-- The uninterpreted sort `U`, the first sort the prelude declares. -/
def sortU : TypeNode := .sort 0

def ufAtoms : Array Node := #[.var "u" sortU, .var "v" sortU, .var "w" sortU]

/-- A random term of sort `U`, over `u`, `v`, `w` and `(f : U → U)`. -/
def genU : Nat → GenM Node
  | 0 => return ufAtoms[← pick ufAtoms.size]!
  | d + 1 => do
    if (← pick 3) == 0 then
      return .app (.node .APPLY_UF (.var "f" (.function sortU sortU))) #[← genU d]
    genU 0

/-- A random equality or `distinct` of terms of sort `U`, or `distinct` of
Booleans or integers. -/
def genUfAtom : GenM Node := do
  match ← pick 6 with
  | 0 | 1 => return eqNode (← genU 2) (← genU 2)
  | 2 | 3 => return mkNode .DISTINCT (← (List.range (2 + (← pick 3))).toArray.mapM fun _ => genU 1)
  | 4 => return mkNode .DISTINCT (← (List.range (2 + (← pick 2))).toArray.mapM fun _ =>
      return atoms[← pick 5]!)
  | _ => return mkNode .DISTINCT (← (List.range (2 + (← pick 2))).toArray.mapM fun _ =>
      return intAtoms[← pick 4]!)

def bvAtoms : Array Node :=
  #[.var "bx" (.bitVector 4), .var "by" (.bitVector 4), .var "bz" (.bitVector 4),
    .const (.bitVector 4 0), .const (.bitVector 4 1), .const (.bitVector 4 15),
    .const (.bitVector 4 5)]

mutual
/-- A random term of sort `(_ BitVec 4)`. -/
partial def genBv : Nat → GenM Node
  | 0 => return bvAtoms[← pick bvAtoms.size]!
  | d + 1 => do
    let bin := #[Kind.BITVECTOR_AND, .BITVECTOR_OR, .BITVECTOR_XOR, .BITVECTOR_ADD,
      .BITVECTOR_MULT, .BITVECTOR_SUB, .BITVECTOR_UDIV, .BITVECTOR_UREM, .BITVECTOR_SHL,
      .BITVECTOR_LSHR, .BITVECTOR_ASHR, .BITVECTOR_NAND, .BITVECTOR_NOR, .BITVECTOR_XNOR,
      .BITVECTOR_SDIV, .BITVECTOR_SREM, .BITVECTOR_SMOD]
    match ← pick 12 with
    | 0 | 1 => genBv 0
    | 2 => return mkNode .BITVECTOR_NOT #[← genBv d]
    | 3 => return mkNode .BITVECTOR_NEG #[← genBv d]
    | 8 =>
      -- `zero_extend` or `sign_extend` of an extract of width 2, or `repeat` of it
      let lo ← pick 3
      let x := mkIndexedNode .BITVECTOR_EXTRACT #[lo + 1, lo] #[← genBv d]
      let k := #[Kind.BITVECTOR_ZERO_EXTEND, .BITVECTOR_SIGN_EXTEND, .BITVECTOR_REPEAT][← pick 3]!
      return mkIndexedNode k #[2] #[x]
    | 9 => return mkNode .BITVECTOR_ITE #[← genBv1 d, ← genBv d, ← genBv d]
    | 10 =>
      -- a bit of width 1, extended to width 4
      return mkIndexedNode .BITVECTOR_ZERO_EXTEND #[3] #[← genBv1 d]
    | 4 =>
      -- `concat` of two extracts of width 2
      let lo ← pick 3
      return mkNode .BITVECTOR_CONCAT #[mkIndexedNode .BITVECTOR_EXTRACT #[lo + 1, lo] #[← genBv d],
        mkIndexedNode .BITVECTOR_EXTRACT #[1, 0] #[← genBv d]]
    | 5 =>
      let k := #[Kind.BITVECTOR_ROTATE_LEFT, .BITVECTOR_ROTATE_RIGHT][← pick 2]!
      return mkIndexedNode k #[(← pick 5 : Nat)] #[← genBv d]
    | _ => return mkNode bin[← pick bin.size]! #[← genBv d, ← genBv d]

/-- A random term of sort `(_ BitVec 1)`. -/
partial def genBv1 : Nat → GenM Node
  | 0 => return #[Node.const (.bitVector 1 0), .const (.bitVector 1 1)][← pick 2]!
  | d + 1 => do
    match ← pick 5 with
    | 0 => genBv1 0
    | 1 => return mkNode .BITVECTOR_COMP #[← genBv d, ← genBv d]
    | 2 => return mkNode .BITVECTOR_REDOR #[← genBv d]
    | 3 => return mkNode .BITVECTOR_REDAND #[← genBv d]
    | _ => let i ← pick 4; return mkIndexedNode .BITVECTOR_EXTRACT #[i, i] #[← genBv d]
end

/-- A random comparison of bit-vector terms. -/
def genBvAtom (d : Nat) : GenM Node := do
  if (← pick 8) == 0 then
    let k := #[Kind.BITVECTOR_UADDO, .BITVECTOR_SADDO, .BITVECTOR_UMULO, .BITVECTOR_SMULO,
      .BITVECTOR_USUBO, .BITVECTOR_SSUBO, .BITVECTOR_SDIVO][← pick 7]!
    return mkNode k #[← genBv d, ← genBv d]
  if (← pick 10) == 0 then return mkNode .BITVECTOR_NEGO #[← genBv d]
  let k := #[Kind.EQUAL, .BITVECTOR_ULT, .BITVECTOR_ULE, .BITVECTOR_UGT, .BITVECTOR_UGE,
    .BITVECTOR_SLT, .BITVECTOR_SLE, .BITVECTOR_SGT, .BITVECTOR_SGE][← pick 9]!
  return mkNode k #[← genBv d, ← genBv d]

def arrT : TypeNode := .array .integer .integer

/-- A random index or element: an integer variable or constant, or `x + 1`. -/
def genIdx : GenM Node := do
  match ← pick 6 with
  | 0 => return .var "x" .integer
  | 1 => return .var "y" .integer
  | 2 => return .const (.integer 0)
  | 3 => return .const (.integer 1)
  | 4 => return .const (.integer 2)
  | _ => return mkNode .ADD #[.var "x" .integer, .const (.integer 1)]

mutual
/-- A random array of sort `(Array Int Int)`, over `aa` and `ab`. -/
partial def genArr : Nat → GenM Node
  | 0 => return #[Node.var "aa" arrT, .var "ab" arrT][← pick 2]!
  | d + 1 => do
    if (← pick 3) == 0 then genArr 0
    else return mkNode .STORE #[← genArr d, ← genIdx, ← genElem d]

/-- A random element: an index-like term or a `select`. -/
partial def genElem : Nat → GenM Node
  | 0 => genIdx
  | d + 1 => do
    if (← pick 2) == 0 then genIdx else return mkNode .SELECT #[← genArr d, ← genIdx]
end

/-- A random equality of arrays or of elements. -/
def genArrAtom : GenM Node := do
  if (← pick 3) == 0 then return eqNode (← genArr 3) (← genArr 3)
  return eqNode (mkNode .SELECT #[← genArr 3, ← genIdx]) (← genElem 2)

/-! ## Sets -/

def setT : TypeNode := .set .integer

/-- A random set of sort `(Set Int)`, over `sa`, `sb` and elements `genIdx`. -/
partial def genSet : Nat → GenM Node
  | 0 => do
    match ← pick 4 with
    | 0 => return .var "sa" setT
    | 1 => return .var "sb" setT
    | 2 => return .const (.emptySet .integer)
    | _ => return mkNode .SET_SINGLETON #[← genIdx]
  | d + 1 => do
    match ← pick 6 with
    | 0 => genSet 0
    | 1 => return mkNode .SET_UNION #[← genSet d, ← genSet d]
    | 2 => return mkNode .SET_INTER #[← genSet d, ← genSet d]
    | 3 => return mkNode .SET_MINUS #[← genSet d, ← genSet d]
    | 4 => return mkNode .SET_INSERT #[← genIdx, ← genSet d]
    | _ => return mkNode .SET_SINGLETON #[← genIdx]

/-- A random set predicate. -/
def genSetAtom : GenM Node := do
  match ← pick 7 with
  | 0 | 1 => return mkNode .SET_MEMBER #[← genIdx, ← genSet 3]
  | 2 => return mkNode .SET_SUBSET #[← genSet 2, ← genSet 2]
  | 3 => return eqNode (← genSet 2) (← genSet 2)
  | 4 => return mkNode .SET_IS_EMPTY #[← genSet 2]
  | 5 => return mkNode .SET_IS_SINGLETON #[← genSet 2]
  | _ => return eqNode (mkNode .SET_CHOOSE #[← genSet 2]) (← genIdx)

/-! ## Datatypes -/

/-- `(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))` -/
def lstT : TypeNode :=
  .datatype "Lst" (.cons "Lst" (.sum .unit (.sum (.cons .integer (.cons (.typeRef "Lst") .unit)) .null)) .nil)

/-- `(declare-datatype Color ((red) (green) (blue)))` -/
def colorT : TypeNode :=
  .datatype "Color" (.cons "Color" (.sum .unit (.sum .unit (.sum .unit .null))) .nil)

/-- `(Pair Int Color)`, for
`(declare-datatypes ((Pair 2)) ((par (T S) ((pair (first T) (second S))))))`,
as Logos's parser instantiates it (`.par_k_Pair`). -/
def pairT : TypeNode :=
  .datatype ".par_1_Pair" (.cons ".par_1_Pair" (.sum (.cons .integer (.cons colorT .unit)) .null) .nil)

/-- `(PL Int)`, for
`(declare-datatypes ((PL 1)) ((par (T) ((pnil) (pcons (phd T) (ptl (PL T)))))))`. -/
def plT : TypeNode :=
  .datatype ".par_2_PL" (.cons ".par_2_PL"
    (.sum .unit (.sum (.cons .integer (.cons (.typeRef ".par_2_PL") .unit)) .null)) .nil)

/-- `(Tuple Int Color)` and `(Tuple Int Int)`. -/
def tupT : TypeNode := .mkTuple [.integer, colorT]
def tupII : TypeNode := .mkTuple [.integer, .integer]

def dtNames : DtNames where
  cons d i := match d, i with
    | "Lst", 0 => some "nil" | "Lst", 1 => some "cons"
    | "Color", 0 => some "red" | "Color", 1 => some "green" | "Color", 2 => some "blue"
    | "Pair", 0 => some "pair"
    | "PL", 0 => some "pnil" | "PL", 1 => some "pcons"
    | _, _ => none
  sel d i j := match d, i, j with
    | "Lst", 1, 0 => some "head" | "Lst", 1, 1 => some "tail"
    | "Pair", 0, 0 => some "first" | "Pair", 0, 1 => some "second"
    | "PL", 1, 0 => some "phd" | "PL", 1, 1 => some "ptl"
    | _, _, _ => none
  sort i := if i == 0 then some "U" else none
  template d := match d with
    | "Pair" => some (2, [[.param 0, .param 1]])
    | "PL" => some (1, [[], [.param 0, .app "PL" [.param 0]]])
    | _ => none

def dtApp (k : Kind) (c : Const) (cs : Array Node) : Node := .app (.node k (.const c)) cs
def lstNil : Node := dtApp .APPLY_CONSTRUCTOR (.dtCons lstT 0) #[]
def lstCons (h t : Node) : Node := dtApp .APPLY_CONSTRUCTOR (.dtCons lstT 1) #[h, t]

mutual
/-- A random list, over `la`, `lb`, `nil`, `cons`, `tail` and updaters. -/
partial def genLst : Nat → GenM Node
  | 0 => do
    match ← pick 4 with
    | 0 => return .var "la" lstT
    | 1 => return .var "lb" lstT
    | 2 => return lstNil
    | _ => return lstCons (← genIdx) (#[Node.var "la" lstT, .var "lb" lstT, lstNil][← pick 3]!)
  | d + 1 => do
    match ← pick 6 with
    | 0 => genLst 0
    | 1 | 2 => return lstCons (← genLstInt d) (← genLst d)
    | 3 => return dtApp .APPLY_SELECTOR (.dtSel lstT 1 1) #[← genLst d]
    | 4 => return dtApp .APPLY_UPDATER (.dtSel lstT 1 0) #[← genLst d, ← genIdx]
    | _ => return dtApp .APPLY_UPDATER (.dtSel lstT 1 1) #[← genLst d, ← genLst d]

/-- A random integer: an index, or the `head` of a list. -/
partial def genLstInt : Nat → GenM Node
  | 0 => genIdx
  | d + 1 => do
    if (← pick 2) == 0 then genIdx else return dtApp .APPLY_SELECTOR (.dtSel lstT 1 0) #[← genLst d]
end

def genColor : GenM Node := do
  match ← pick 4 with
  | 3 => return .var "co" colorT
  | i => return dtApp .APPLY_CONSTRUCTOR (.dtCons colorT i) #[]

mutual
/-- A random `(Pair Int Color)`: `pa`, `pair`, an updater, or a tuple's field
as an integer. -/
partial def genPair : Nat → GenM Node
  | 0 => do
    if (← pick 2) == 0 then return .var "pa" pairT
    else return dtApp .APPLY_CONSTRUCTOR (.dtCons pairT 0) #[← genIdx, ← genColor]
  | d + 1 => do
    match ← pick 4 with
    | 0 => genPair 0
    | 1 => return dtApp .APPLY_CONSTRUCTOR (.dtCons pairT 0) #[← genDtInt d, ← genColor]
    | 2 => return dtApp .APPLY_UPDATER (.dtSel pairT 0 0) #[← genPair d, ← genDtInt d]
    | _ => return dtApp .APPLY_UPDATER (.dtSel pairT 0 1) #[← genPair d, ← genColor]

/-- A random `(PL Int)`. -/
partial def genPL : Nat → GenM Node
  | 0 => do
    match ← pick 3 with
    | 0 => return .var "pl" plT
    | 1 => return dtApp .APPLY_CONSTRUCTOR (.dtCons plT 0) #[]
    | _ => return dtApp .APPLY_CONSTRUCTOR (.dtCons plT 1) #[← genIdx, .var "pl" plT]
  | d + 1 => do
    match ← pick 4 with
    | 0 => genPL 0
    | 1 | 2 => return dtApp .APPLY_CONSTRUCTOR (.dtCons plT 1) #[← genDtInt d, ← genPL d]
    | _ => return dtApp .APPLY_SELECTOR (.dtSel plT 1 1) #[← genPL d]

/-- A random `(Tuple Int Color)`: `tp`, a tuple, or an update. -/
partial def genTup : Nat → GenM Node
  | 0 => do
    if (← pick 2) == 0 then return .var "tp" tupT
    else return DatatypesRewriter.mkTupleNode [← genIdx, ← genColor]
  | d + 1 => do
    match ← pick 4 with
    | 0 => genTup 0
    | 1 => return DatatypesRewriter.mkTupleNode [← genDtInt d, ← genColor]
    | 2 => return mkIndexedNode .TUPLE_UPDATE #[0] #[← genTup d, ← genDtInt d]
    | _ => return mkIndexedNode .TUPLE_UPDATE #[1] #[← genTup d, ← genColor]

/-- A random `(Tuple Int Int)`. -/
partial def genTupII : Nat → GenM Node
  | 0 => do
    if (← pick 2) == 0 then return .var "tq" tupII
    else return DatatypesRewriter.mkTupleNode [← genIdx, ← genIdx]
  | d + 1 => do
    match ← pick 3 with
    | 0 => genTupII 0
    | 1 => return DatatypesRewriter.mkTupleNode [← genDtInt d, ← genDtInt d]
    | _ => return mkIndexedNode .TUPLE_UPDATE #[← pick 2] #[← genTupII d, ← genDtInt d]

/-- A random integer from these datatypes: an index, a selector, or a tuple's
field. -/
partial def genDtInt : Nat → GenM Node
  | 0 => genIdx
  | d + 1 => do
    match ← pick 5 with
    | 0 | 1 => genIdx
    | 2 => return dtApp .APPLY_SELECTOR (.dtSel pairT 0 0) #[← genPair d]
    | 3 => return mkIndexedNode .TUPLE_SELECT #[0] #[← genTup d]
    | _ => return mkIndexedNode .TUPLE_SELECT #[← pick 2] #[← genTupII d]
end

/-- A random datatype predicate. -/
def genDtAtom : GenM Node := do
  match ← pick 14 with
  | 0 | 1 => return eqNode (← genLst 2) (← genLst 2)
  | 2 => return dtApp .APPLY_TESTER (.dtCons lstT (← pick 2)) #[← genLst 3]
  | 3 => return eqNode (← genLstInt 3) (← genIdx)
  | 4 => return eqNode (← genColor) (← genColor)
  | 5 => return dtApp .APPLY_TESTER (.dtCons colorT (← pick 3)) #[← genColor]
  | 6 => return eqNode (← genPair 2) (← genPair 2)
  | 7 => return eqNode (dtApp .APPLY_SELECTOR (.dtSel pairT 0 1) #[← genPair 2]) (← genColor)
  | 8 => return eqNode (← genPL 2) (← genPL 2)
  | 9 => return dtApp .APPLY_TESTER (.dtCons plT (← pick 2)) #[← genPL 3]
  | 10 => return eqNode (dtApp .APPLY_SELECTOR (.dtSel plT 1 0) #[← genPL 2]) (← genDtInt 2)
  | 11 => return eqNode (← genTup 2) (← genTup 2)
  | 12 => return eqNode (mkIndexedNode .TUPLE_SELECT #[1] #[← genTup 2]) (← genColor)
  | _ => return eqNode (← genTupII 2) (← genTupII 2)

/-! ## Quantifiers -/

/-- The bound variables quantified formulas use, never shadowed. -/
def qVars : Array Node :=
  #[.boundVar "qx" .integer, .boundVar "qy" .integer, .boundVar "qb" .boolean, .boundVar "qu" sortU]

/-- A random integer term over the bound variables in scope `vs` and `x`, `y`. -/
def genQInt (vs : List Node) : GenM Node := do
  let ints := vs.filter (·.typeHint == some .integer)
  let pool := ints.toArray ++ #[.var "x" .integer, .var "y" .integer, .const (.integer 0),
    .const (.integer 1)]
  let t := pool[← pick pool.size]!
  if (← pick 4) == 0 then return mkNode .ADD #[t, .const (.integer 1)] else return t

/-- A random atom over the bound variables in scope. -/
def genQAtom (vs : List Node) : GenM Node := do
  let us := vs.filter (·.typeHint == some sortU)
  let bs := vs.filter (·.typeHint == some .boolean)
  let f := Node.var "f" (.function sortU sortU)
  match ← pick 7 with
  | 0 | 1 => return mkNode .GEQ #[← genQInt vs, ← genQInt vs]
  | 2 => return eqNode (← genQInt vs) (← genQInt vs)
  | 3 => match bs with
    | b :: _ => return b
    | [] => return atoms[← pick 3]!
  | 4 => match us with
    | u :: _ => return eqNode u (#[Node.var "u" sortU, .var "v" sortU][← pick 2]!)
    | [] => return atoms[← pick 3]!
  | 5 => match us with
    | u :: _ => return eqNode (.app (.node .APPLY_UF f) #[u]) (.var "v" sortU)
    | [] => return eqNode (← genQInt vs) (← genQInt vs)
  | _ => return atoms[← pick atoms.size]!

mutual
/-- A random quantified formula, binding some of the variables `avail`. -/
partial def genQuant (avail : List Node) (vs : List Node) (d : Nat) : GenM Node := do
  if avail.isEmpty then return ← genQAtom vs
  let n := 1 + (← pick (min 2 avail.length))
  -- `n` variables of `avail`, from a random start
  let i ← pick avail.length
  let bound := ((avail.drop i) ++ avail.take i).take n
  let rest := avail.filter (!bound.contains ·)
  let body ← genQBody rest (vs ++ bound) d
  let k := if (← pick 3) == 0 then Kind.EXISTS else .FORALL
  return mkNode k #[mkNode .BOUND_VAR_LIST bound.toArray, body]

/-- A random body over the bound variables in scope `vs`. -/
partial def genQBody (avail : List Node) (vs : List Node) : Nat → GenM Node
  | 0 => genQAtom vs
  | d + 1 => do
    match ← pick 9 with
    | 0 | 1 => genQAtom vs
    | 2 => return notNode (← genQBody avail vs d)
    | 3 => return mkNode .AND (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genQBody avail vs d)
    | 4 => return mkNode .OR (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genQBody avail vs d)
    | 5 => return mkNode .IMPLIES #[← genQBody avail vs d, ← genQBody avail vs d]
    | 6 => return iteNode (← genQBody avail vs d) (← genQBody avail vs d) (← genQBody avail vs d)
    | _ => genQuant avail vs d
end

def genQuantAtom : GenM Node := genQuant qVars.toList [] 3

/-! ## Strings -/

def strLit (w : String) : Node := .const (.string (w.toList.map Char.toNat))

def strAtoms : Array Node :=
  #[.var "su" .string, .var "sv" .string, strLit "", strLit "a", strLit "ab", strLit "b"]

def smallInts : Array Node :=
  #[.const (.integer 0), .const (.integer 1), .const (.integer 2), .var "x" .integer]

mutual
/-- A random string term over `s`, `t` and a few constants. -/
partial def genStr : Nat → GenM Node
  | 0 => return strAtoms[← pick strAtoms.size]!
  | d + 1 => do
    match ← pick 9 with
    | 0 | 1 => genStr 0
    | 2 => return mkNode .STRING_CONCAT (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genStr d)
    | 3 => return mkNode .STRING_SUBSTR #[← genStr d, smallInts[← pick 4]!, smallInts[← pick 4]!]
    | 4 => return mkNode .STRING_CHARAT #[← genStr d, smallInts[← pick 4]!]
    | 5 => return mkNode .STRING_REPLACE #[← genStr d, ← genStr 0, ← genStr 0]
    | 6 => return mkNode .STRING_REV #[← genStr d]
    | 7 => return mkNode .STRING_ITOS #[← genStrInt d]
    | _ => return mkNode .STRING_REPLACE_ALL #[← genStr d, ← genStr 0, ← genStr 0]

/-- A random integer term about strings. -/
partial def genStrInt : Nat → GenM Node
  | 0 => return smallInts[← pick 4]!
  | d + 1 => do
    match ← pick 4 with
    | 0 => return mkNode .STRING_LENGTH #[← genStr d]
    | 1 => return mkNode .STRING_INDEXOF #[← genStr d, ← genStr 0, smallInts[← pick 4]!]
    | 2 => return mkNode .STRING_STOI #[← genStr d]
    | _ => genStrInt 0
end

/-- A random regular expression. -/
partial def genRe : Nat → GenM Node
  | 0 => do
    match ← pick 4 with
    | 0 => return mkNode .STRING_TO_REGEXP #[← genStr 0]
    | 1 => return mkNode .REGEXP_ALLCHAR #[]
    | 2 => return mkNode .REGEXP_RANGE #[strLit "a", strLit "c"]
    | _ => return mkNode .REGEXP_ALL #[]
  | d + 1 => do
    match ← pick 8 with
    | 0 => return mkNode .REGEXP_STAR #[← genRe d]
    | 1 => return mkNode .REGEXP_CONCAT #[← genRe d, ← genRe d]
    | 2 => return mkNode .REGEXP_UNION #[← genRe d, ← genRe d]
    | 3 => return mkNode .REGEXP_INTER #[← genRe d, ← genRe d]
    | 4 => return mkNode .REGEXP_OPT #[← genRe d]
    | 5 => return mkNode .REGEXP_COMPLEMENT #[← genRe d]
    | 6 => return mkIndexedNode .REGEXP_LOOP #[((← pick 3 : Nat) : Int), ((← pick 3 : Nat) : Int)] #[← genRe d]
    | _ => genRe 0

/-- A random string predicate. -/
def genStrAtom : GenM Node := do
  match ← pick 7 with
  | 0 => return eqNode (← genStr 2) (← genStr 2)
  | 1 => return mkNode .STRING_CONTAINS #[← genStr 2, ← genStr 1]
  | 2 => return mkNode .STRING_PREFIX #[← genStr 1, ← genStr 2]
  | 3 => return mkNode .STRING_SUFFIX #[← genStr 1, ← genStr 2]
  | 4 => return eqNode (← genStrInt 2) (← genStrInt 1)
  | 5 => return mkNode .STRING_IN_REGEXP #[← genStr 1, ← genRe 2]
  | _ => return mkNode .STRING_LEQ #[← genStr 1, ← genStr 1]

/-! ## Mixed theories -/

def bvArrT : TypeNode := .array (.bitVector 4) .integer
def uArrT : TypeNode := .array sortU sortU

/-- A random array from bit-vectors to integers, over `am`: indices are
bit-vector terms, so their equalities are decided by the bit-vector rewriter. -/
partial def genBvArr : Nat → GenM Node
  | 0 => return .var "am" bvArrT
  | d + 1 => do
    if (← pick 3) == 0 then genBvArr 0
    else return mkNode .STORE #[← genBvArr d, ← genBv 1, ← genArith false 1]

/-- A random array over `U`, over `bm` and `cm`. -/
partial def genUArr : Nat → GenM Node
  | 0 => return #[Node.var "bm" uArrT, .var "cm" uArrT][← pick 2]!
  | d + 1 => do
    if (← pick 3) == 0 then genUArr 0
    else return mkNode .STORE #[← genUArr d, ← genU 1, ← genU 1]

/-- A random term of sort `U` that may read an array or apply `f` to one. -/
def genUMixed (d : Nat) : GenM Node := do
  match ← pick 4 with
  | 0 => return mkNode .SELECT #[← genUArr d, ← genU 1]
  | 1 => return .app (.node .APPLY_UF (.var "f" (.function sortU sortU))) #[mkNode .SELECT #[← genUArr d, ← genU 0]]
  | _ => genU 1

/-- A random atom mixing theories. -/
def genMixedAtom (cond : Node) : GenM Node := do
  match ← pick 9 with
  | 0 => return eqNode (mkNode .SELECT #[← genBvArr 2, ← genBv 1]) (← genArith false 1)
  | 1 => return eqNode (← genBvArr 2) (← genBvArr 2)
  | 2 => return eqNode (← genUMixed 2) (← genUMixed 2)
  | 3 => return eqNode (← genUArr 2) (← genUArr 2)
  | 4 => return mkNode .DISTINCT #[← genUArr 1, ← genUArr 1, ← genUArr 1]
  | 5 => return eqNode (iteNode cond (← genBv 1) (← genBv 1)) (← genBv 1)
  | 6 => return eqNode (iteNode cond (← genUMixed 1) (← genUMixed 1)) (← genUMixed 1)
  | 7 => return mkNode .BITVECTOR_ULT #[mkIndexedNode .INT_TO_BITVECTOR #[4] #[← genArith false 1], ← genBv 1]
  | _ => return eqNode (iteNode cond (mkNode .SELECT #[← genBvArr 1, ← genBv 0]) (← genArith false 1)) (← genArith false 1)

/-- A random comparison of arithmetic terms. -/
def genCmp (d : Nat) : GenM Node := do
  if (← pick 10) == 0 then return mkNode .IS_INTEGER #[← genArith true d]
  let real := (← pick 2) == 0
  let k := #[Kind.GEQ, .LEQ, .GT, .LT, .EQUAL][← pick 5]!
  return mkNode k #[← genArith real d, ← genArith real d]

def genBool (arith : Bool) (uf : Bool := false) (bv : Bool := false) (arr : Bool := false)
    (mixed : Bool := false) (str : Bool := false) (sets : Bool := false) (dt : Bool := false) (quant : Bool := false) : Nat → GenM Node
  | 0 => do
    if arith && (← pick 2) == 0 then return ← genCmp 1
    if uf then
      if (← pick 2) == 0 then return ← genUfAtom
    if bv then
      if (← pick 3) != 0 then return ← genBvAtom 2
    if arr then
      if (← pick 3) != 0 then return ← genArrAtom
    if mixed then
      if (← pick 4) != 0 then return ← genMixedAtom atoms[← pick atoms.size]!
    if str then
      if (← pick 4) != 0 then return ← genStrAtom
    if sets then
      if (← pick 4) != 0 then return ← genSetAtom
    if dt then
      if (← pick 4) != 0 then return ← genDtAtom
    if quant then
      if (← pick 3) != 0 then return ← genQuantAtom
    return atoms[← pick atoms.size]!
  | d + 1 => do
    match ← pick 11 with
    | 0 | 1 => genBool arith uf bv arr mixed str sets dt quant 0
    | 2 => return notNode (← genBool arith uf bv arr mixed str sets dt quant d)
    | 3 => return mkNode .AND (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool arith uf bv arr mixed str sets dt quant d)
    | 4 => return mkNode .OR (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool arith uf bv arr mixed str sets dt quant d)
    | 5 => return mkNode .IMPLIES #[← genBool arith uf bv arr mixed str sets dt quant d, ← genBool arith uf bv arr mixed str sets dt quant d]
    | 6 => return mkNode .XOR #[← genBool arith uf bv arr mixed str sets dt quant d, ← genBool arith uf bv arr mixed str sets dt quant d]
    | 7 => return eqNode (← genBool arith uf bv arr mixed str sets dt quant d) (← genBool arith uf bv arr mixed str sets dt quant d)
    | 8 => if arith then genCmp d else genBool arith uf bv arr mixed str sets dt quant d
    | _ => return iteNode (← genBool arith uf bv arr mixed str sets dt quant d) (← genBool arith uf bv arr mixed str sets dt quant d) (← genBool arith uf bv arr mixed str sets dt quant d)

def main (args : List String) : IO Unit := do
  let profile := args.contains "--profile"
  let args := args.filter (· != "--profile")
  if profile then Profile.enable
  let seed := (args[0]? >>= String.toNat?).getD 1
  let count := (args[1]? >>= String.toNat?).getD 100
  let depth := (args[2]? >>= String.toNat?).getD 3
  let arith := args[3]? == some "arith"
  let uf := args[3]? == some "uf"
  let bv := args[3]? == some "bv"
  let arr := args[3]? == some "arrays"
  let mixed := args[3]? == some "mixed"
  let str := args[3]? == some "strings"
  let sets := args[3]? == some "sets"
  let dt := args[3]? == some "datatypes"
  let quant := args[3]? == some "quantifiers"
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [0:count] do
    let (t, r) := (genBool arith uf bv arr mixed str sets dt quant depth).run rng
    rng := r
    let r ← Profile.measure "total" "rewrite" fun _ => rewrite t
    IO.println s!"{t.toSmtLibWith dtNames}\t{r.toSmtLibWith dtNames}"
  if profile then Profile.report
