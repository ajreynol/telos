import Telos

/-!
# `telos-fuzz`: random terms and their rewrites

`telos-fuzz SEED COUNT` prints `COUNT` random Boolean terms over `a`, `b`, `c`
(and the integer `x`), each with its telos rewrite, as `input<TAB>output` lines.
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

def genBool : Nat → GenM Node
  | 0 => do return atoms[← pick atoms.size]!
  | d + 1 => do
    match ← pick 10 with
    | 0 | 1 => return atoms[← pick atoms.size]!
    | 2 => return notNode (← genBool d)
    | 3 => return mkNode .AND (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool d)
    | 4 => return mkNode .OR (← (List.range (2 + (← pick 2))).toArray.mapM fun _ => genBool d)
    | 5 => return mkNode .IMPLIES #[← genBool d, ← genBool d]
    | 6 => return mkNode .XOR #[← genBool d, ← genBool d]
    | 7 => return eqNode (← genBool d) (← genBool d)
    | _ => return iteNode (← genBool d) (← genBool d) (← genBool d)

def main (args : List String) : IO Unit := do
  let seed := (args[0]? >>= String.toNat?).getD 1
  let count := (args[1]? >>= String.toNat?).getD 100
  let depth := (args[2]? >>= String.toNat?).getD 3
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [0:count] do
    let (t, r) := (genBool depth).run rng
    rng := r
    IO.println s!"{t.toSmtLib}\t{(rewrite t).toSmtLib}"
