def hello : String := "hello"

def fo : BitVec 5 := BitVec.ofNat 5 10

/-!

## Packed Floating Point Numbers

-/

/--
A packed floating point number,
whose exponent and significand width are encoded at the type level.
-/
structure PackedFloat (exWidth : Nat) (sigWidth : Nat) where
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Mantissa of the packed float. -/
    sig : BitVec sigWidth
    /-- Sign bit. -/
    sign : BitVec 1
deriving DecidableEq, Repr

/-
def foo : PackedFloat 1 1 where
  ex := 1#1
  sig := 0#1
  sign := 0#1
#eval (repr foo)
-/

structure FixedPoint (width : Nat) (exOffset : Nat) where
    val : BitVec width
    hExOffset : exOffset < width

deriving DecidableEq, Repr

namespace PackedFloat
def toFixed (he : 0 < e) (pf : PackedFloat e s) : FixedPoint (2 ^ e + s) (2^(e-1) + s) where
  val := sorry
  hExOffset := by
    rcases e with _ | n
    · omega
    · simp only [Nat.add_one_sub_one, Nat.add_lt_add_iff_right]
      apply Nat.pow_lt_pow_of_lt <;> simp


/-# Contents of File

- @bollu assigns assignment: Setup CI!
- Definitions of PackedFloat and FixedPoint representations
- Conversion from PackedFloat to FixedPoint
- (next step: in another file called Fp.FixedPoint, create addition and multiplication)
- (@bollu's thought): We may like to have `FixedPoint.toRat : FixedPoint → ℚ`, which
  interprets the FP as a rational.

-/
#check toFixed
end PackedFloat
