import Telos

/-!
# `telos-fuzz`: random terms and their rewrites

`telos-fuzz SEED COUNT DEPTH [arith|uf|bv] [--profile]` prints `COUNT` random Boolean terms over
`a`, `b`, `c` (and the integer `x`), each with its telos rewrite, as
`input<TAB>output` lines. With `arith`, the terms also contain comparisons of
integer and real terms over `x`, `y`, `r` and `s`. With `uf`, they also contain
equalities and `distinct` of terms of an uninterpreted sort `U` over `u`, `v`,
`w` and `f`, and `distinct` of Booleans and integers. With `bv`, they also
contain comparisons of terms of sort `(_ BitVec 4)` over `bx`, `by` and `bz`.
`scripts/fuzz.py` compares them against cvc5's rewriter. With `--profile`, a table
of where the rewriting time went is printed to standard error
(`Telos/Profile.lean`); `scripts/profile.sh` runs a standard benchmark.
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

/-- A random term of sort `(_ BitVec 4)`. -/
partial def genBv : Nat → GenM Node
  | 0 => return bvAtoms[← pick bvAtoms.size]!
  | d + 1 => do
    let bin := #[Kind.BITVECTOR_AND, .BITVECTOR_OR, .BITVECTOR_XOR, .BITVECTOR_ADD,
      .BITVECTOR_MULT, .BITVECTOR_SUB, .BITVECTOR_UDIV, .BITVECTOR_UREM, .BITVECTOR_SHL,
      .BITVECTOR_LSHR, .BITVECTOR_ASHR, .BITVECTOR_NAND, .BITVECTOR_NOR, .BITVECTOR_XNOR,
      .BITVECTOR_SDIV, .BITVECTOR_SREM, .BITVECTOR_SMOD]
    match ← pick 8 with
    | 0 | 1 => genBv 0
    | 2 => return mkNode .BITVECTOR_NOT #[← genBv d]
    | 3 => return mkNode .BITVECTOR_NEG #[← genBv d]
    | 4 =>
      -- `concat` of two extracts of width 2
      let lo ← pick 3
      return mkNode .BITVECTOR_CONCAT #[mkIndexedNode .BITVECTOR_EXTRACT #[lo + 1, lo] #[← genBv d],
        mkIndexedNode .BITVECTOR_EXTRACT #[1, 0] #[← genBv d]]
    | 5 =>
      let k := #[Kind.BITVECTOR_ROTATE_LEFT, .BITVECTOR_ROTATE_RIGHT][← pick 2]!
      return mkIndexedNode k #[(← pick 5 : Nat)] #[← genBv d]
    | _ => return mkNode bin[← pick bin.size]! #[← genBv d, ← genBv d]

/-- A random comparison of bit-vector terms. -/
def genBvAtom (d : Nat) : GenM Node := do
  let k := #[Kind.EQUAL, .BITVECTOR_ULT, .BITVECTOR_ULE, .BITVECTOR_UGT, .BITVECTOR_UGE,
    .BITVECTOR_SLT, .BITVECTOR_SLE, .BITVECTOR_SGT, .BITVECTOR_SGE][← pick 9]!
  return mkNode k #[← genBv d, ← genBv d]

/-- A random comparison of arithmetic terms. -/
def genCmp (d : Nat) : GenM Node := do
  if (← pick 10) == 0 then return mkNode .IS_INTEGER #[← genArith true d]
  let real := (← pick 2) == 0
  let k := #[Kind.GEQ, .LEQ, .GT, .LT, .EQUAL][← pick 5]!
  return mkNode k #[← genArith real d, ← genArith real d]

def genBool (arith : Bool) (uf : Bool := false) (bv : Bool := false) : Nat → GenM Node
  | 0 => do
    if arith && (← pick 2) == 0 then return ← genCmp 1
    if uf then
      if (← pick 2) == 0 then return ← genUfAtom
    if bv then
      if (← pick 3) != 0 then return ← genBvAtom 2
    return atoms[← pick atoms.size]!
  | d + 1 => do
    match ← pick 11 with
    | 0 | 1 => genBool arith uf bv 0
    | 2 => return notNode (← genBool arith uf bv d)
    | 3 => return mkNode .AND (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool arith uf bv d)
    | 4 => return mkNode .OR (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool arith uf bv d)
    | 5 => return mkNode .IMPLIES #[← genBool arith uf bv d, ← genBool arith uf bv d]
    | 6 => return mkNode .XOR #[← genBool arith uf bv d, ← genBool arith uf bv d]
    | 7 => return eqNode (← genBool arith uf bv d) (← genBool arith uf bv d)
    | 8 => if arith then genCmp d else genBool arith uf bv d
    | _ => return iteNode (← genBool arith uf bv d) (← genBool arith uf bv d) (← genBool arith uf bv d)

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
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [0:count] do
    let (t, r) := (genBool arith uf bv depth).run rng
    rng := r
    let r ← Profile.measure "total" "rewrite" fun _ => rewrite t
    IO.println s!"{t.toSmtLib}\t{r.toSmtLib}"
  if profile then Profile.report
