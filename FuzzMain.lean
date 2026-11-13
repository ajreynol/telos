import Telos

/-!
# `telos-fuzz`: random terms and their rewrites

`telos-fuzz SEED COUNT DEPTH [arith]` prints `COUNT` random Boolean terms over
`a`, `b`, `c` (and the integer `x`), each with its telos rewrite, as
`input<TAB>output` lines. With `arith`, the terms also contain comparisons of
integer and real terms over `x`, `y`, `r` and `s`.
`scripts/fuzz.py` compares them against cvc5's rewriter.
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

/-- A random comparison of arithmetic terms. -/
def genCmp (d : Nat) : GenM Node := do
  if (← pick 10) == 0 then return mkNode .IS_INTEGER #[← genArith true d]
  let real := (← pick 2) == 0
  let k := #[Kind.GEQ, .LEQ, .GT, .LT, .EQUAL][← pick 5]!
  return mkNode k #[← genArith real d, ← genArith real d]

def genBool (arith : Bool) : Nat → GenM Node
  | 0 => do
    if arith && (← pick 2) == 0 then return ← genCmp 1
    return atoms[← pick atoms.size]!
  | d + 1 => do
    match ← pick 11 with
    | 0 | 1 => genBool arith 0
    | 2 => return notNode (← genBool arith d)
    | 3 => return mkNode .AND (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool arith d)
    | 4 => return mkNode .OR (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool arith d)
    | 5 => return mkNode .IMPLIES #[← genBool arith d, ← genBool arith d]
    | 6 => return mkNode .XOR #[← genBool arith d, ← genBool arith d]
    | 7 => return eqNode (← genBool arith d) (← genBool arith d)
    | 8 => if arith then genCmp d else genBool arith d
    | _ => return iteNode (← genBool arith d) (← genBool arith d) (← genBool arith d)

def main (args : List String) : IO Unit := do
  let seed := (args[0]? >>= String.toNat?).getD 1
  let count := (args[1]? >>= String.toNat?).getD 100
  let depth := (args[2]? >>= String.toNat?).getD 3
  let arith := args[3]? == some "arith"
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [0:count] do
    let (t, r) := (genBool arith depth).run rng
    rng := r
    IO.println s!"{t.toSmtLib}\t{(rewrite t).toSmtLib}"
