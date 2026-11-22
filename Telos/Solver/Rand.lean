/-!
# cvc5's random numbers

cvc5's `Random` (`src/util/random.cpp`): a 64-bit Mersenne twister
(`std::mt19937_64`) seeded with `~0` for the default seed `0`; and
`std::shuffle` with it, as libstdc++ (GCC 15) implements it: pairs of swaps
from one draw when the generator's range allows, each draw downscaled by
Lemire's nearly divisionless method (`uniform_int_distribution`).
-/

namespace Telos.Solver

/-- The state of `std::mt19937_64`. -/
structure MT where
  mt : Array UInt64
  idx : Nat
  deriving Inhabited

namespace MT

def n : Nat := 312
def m : Nat := 156

/-- `seed`. -/
def seed (s : UInt64) : MT := Id.run do
  let mut a : Array UInt64 := Array.replicate n 0
  a := a.set! 0 s
  for i in [1:n] do
    let p := a[i - 1]!
    a := a.set! i ((6364136223846793005 : UInt64) * (p ^^^ (p >>> 62)) + i.toUInt64)
  return { mt := a, idx := n }

/-- cvc5's generator, for the default seed. -/
def cvc5 : MT := seed (~~~0)

def twist (s : MT) : MT := Id.run do
  let mut a := s.mt
  for i in [0:n] do
    let x := (a[i]! &&& 0xFFFFFFFF80000000) ||| (a[(i + 1) % n]! &&& 0x7FFFFFFF)
    let xA := if x &&& 1 == 1 then (x >>> 1) ^^^ 0xB5026F5AA96619E9 else x >>> 1
    a := a.set! i (a[(i + m) % n]! ^^^ xA)
  return { mt := a, idx := 0 }

/-- The next number. -/
def next (s : MT) : UInt64 × MT :=
  let s := if s.idx ≥ n then twist s else s
  let y := s.mt[s.idx]!
  let y := y ^^^ ((y >>> 29) &&& 0x5555555555555555)
  let y := y ^^^ ((y <<< 17) &&& 0x71D67FFFEDA60000)
  let y := y ^^^ ((y <<< 37) &&& 0xFFF7EEE000000000)
  let y := y ^^^ (y >>> 43)
  (y, { s with idx := s.idx + 1 })

/-- A number in `[0, r)` (`uniform_int_distribution{0, r - 1}`, Lemire's
method with 128-bit products). -/
partial def below (s : MT) (r : Nat) : Nat × MT :=
  let w := 2 ^ 64
  let (x, s) := s.next
  let p := x.toNat * r
  let low := p % w
  if low < r then
    let threshold := (w - r) % r
    let rec loop (p : Nat) (s : MT) : Nat × MT :=
      if p % w < threshold then
        let (x, s) := s.next
        loop (x.toNat * r) s
      else (p / w, s)
    loop p s
  else (p / w, s)

end MT

/-- `std::shuffle` with the generator (libstdc++). -/
def shuffle {α : Type} [Inhabited α] (a : Array α) (g : MT) : Array α × MT := Id.run do
  let k := a.size
  if k == 0 then return (a, g)
  let mut a := a
  let mut g := g
  -- (the generator's range, 2^64 - 1, over `k` is at least `k`)
  let mut i := 1
  if k % 2 == 0 then
    let (d, g') := g.below 2
    g := g'
    a := a.swapIfInBounds i d
    i := i + 1
  while i < k do
    let sr := i + 1
    let (x, g') := g.below (sr * (sr + 1))
    g := g'
    a := a.swapIfInBounds i (x / (sr + 1))
    a := a.swapIfInBounds (i + 1) (x % (sr + 1))
    i := i + 2
  return (a, g)

end Telos.Solver
