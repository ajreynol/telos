/-!
# Delta-rationals

cvc5's `DeltaRational` (`src/theory/arith/delta_rational.h`): `c + k·δ` for
rationals `c` and `k` and an infinitesimal `δ > 0`, which the simplex uses for
strict bounds (`x < c` is `x ≤ c - δ`). They are ordered lexicographically:
first by `c`, then by `k`.

cvc5 throws on the products and quotients of two delta-rationals that both have
an infinitesimal part; here `mul` and `div` take a rational.
-/

namespace Telos.Solver.Arith

/-- `c + k·δ`. -/
structure DeltaRational where
  /-- The non-infinitesimal part. -/
  c : Rat := 0
  /-- The infinitesimal part (the coefficient of `δ`). -/
  k : Rat := 0
  deriving Inhabited, BEq, Repr

namespace DeltaRational

instance : OfNat DeltaRational n := ⟨{ c := n }⟩
instance : Coe Rat DeltaRational := ⟨fun c => { c }⟩

def ofRat (c : Rat) : DeltaRational := { c }

/-- The sign of a rational, as cvc5's `sgn`. -/
def ratSgn (q : Rat) : Int := if q < 0 then -1 else if q == 0 then 0 else 1

def infinitesimalSgn (d : DeltaRational) : Int := ratSgn d.k
def infinitesimalIsZero (d : DeltaRational) : Bool := d.k == 0
def noninfinitesimalIsZero (d : DeltaRational) : Bool := d.c == 0
def isZero (d : DeltaRational) : Bool := d.c == 0 && d.k == 0

/-- The sign: of `c`, or of `k` if `c` is zero. -/
def sgn (d : DeltaRational) : Int := let s := ratSgn d.c; if s == 0 then d.infinitesimalSgn else s

/-- `cmp`: -1, 0 or 1. -/
def cmp (a b : DeltaRational) : Int :=
  if a.c < b.c then -1 else if b.c < a.c then 1
  else if a.k < b.k then -1 else if b.k < a.k then 1 else 0

instance : Add DeltaRational := ⟨fun a b => ⟨a.c + b.c, a.k + b.k⟩⟩
instance : Neg DeltaRational := ⟨fun a => ⟨-a.c, -a.k⟩⟩
instance : Sub DeltaRational := ⟨fun a b => ⟨a.c - b.c, a.k - b.k⟩⟩
instance : HMul DeltaRational Rat DeltaRational := ⟨fun a q => ⟨q * a.c, q * a.k⟩⟩
instance : HMul Rat DeltaRational DeltaRational := ⟨fun q a => ⟨q * a.c, q * a.k⟩⟩
instance : HDiv DeltaRational Rat DeltaRational := ⟨fun a q => ⟨a.c / q, a.k / q⟩⟩

instance : LT DeltaRational := ⟨fun a b => cmp a b < 0⟩
instance : LE DeltaRational := ⟨fun a b => cmp a b ≤ 0⟩
instance (a b : DeltaRational) : Decidable (a < b) := inferInstanceAs (Decidable (cmp a b < 0))
instance (a b : DeltaRational) : Decidable (a ≤ b) := inferInstanceAs (Decidable (cmp a b ≤ 0))

def abs (d : DeltaRational) : DeltaRational := if d.sgn ≥ 0 then d else -d

/-- The largest integer at most `d` (`DeltaRational::floor`): the floor of `c`,
less one if `c` is an integer and `k < 0`. -/
def floor (d : DeltaRational) : Int :=
  let f := d.c.floor
  if d.c == (f : Rat) && d.k < 0 then f - 1 else f

/-- The smallest integer at least `d` (`DeltaRational::ceiling`). -/
def ceiling (d : DeltaRational) : Int :=
  let f := d.c.ceil
  if d.c == (f : Rat) && d.k > 0 then f + 1 else f

/-- `isIntegral`: no infinitesimal part, and an integer non-infinitesimal part. -/
def isIntegral (d : DeltaRational) : Bool := d.k == 0 && d.c.den == 1

/-- The value of `d` for a value of `δ` (`DeltaRational::substituteDelta`, used
for models). -/
def substituteDelta (d : DeltaRational) (δ : Rat) : Rat := d.c + d.k * δ

instance : ToString DeltaRational := ⟨fun d => if d.k == 0 then toString d.c else s!"{d.c}+{d.k}δ"⟩

end DeltaRational

end Telos.Solver.Arith
