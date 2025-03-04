import Fp.Utils

def hello : String := "hello"

/-!

## Packed Floating Point Numbers

-/

/--
A packed floating point number,
whose exponent and significand width are encoded at the type level.
-/
structure PackedFloat (exWidth : Nat) (sigWidth : Nat) where
    /-- Sign bit. -/
    sign : BitVec 1
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Significand (mantissa) of the packed float. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr


/--
A fixed point number with specified exponent offset.

NOTE: Current implementation may not account for data stored within NaNs.
-/
structure FixedPoint (width : Nat) (exOffset : Nat) where
    sign : BitVec 1
    infinite : BitVec 1
    nan : BitVec 1
    val : BitVec width
    hExOffset : exOffset < width

deriving DecidableEq, Repr

namespace PackedFloat
/--
Returns the "canonical" NaN for the given floating point format. For example, the canonical NaN for `exWidth` and `sigWidth` 4 is
`0.1111.1000`.
-/
def nan (exWidth : Nat) (sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := 0#1
  ex := BitVec.allOnes exWidth
  sig := BitVec.ofNat sigWidth (2 ^ (sigWidth - 1))

def isInfinite (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig == BitVec.zero s

def isNaN (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig != BitVec.zero s

def isZeroOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.zero e

/--
Convert from a packed float to a fixed point number.

Conversion function assumes IEEE compliance. For output `FixedPoint` number to
have a non-degenerate exponent offset, we need two or more bits in the
exponent.

NOTE: Assuming IEEE compliance, you technically only need 2^e + s - 2 bits to
cover the entire range of representable values. Some non-compliant formats have
a slightly larger range of representable exponents, so we allow for two extra
bits of precision.
-/
def toFixed (pf : PackedFloat e s) (he : 0 < e) : FixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2) where
  sign := pf.sign
  infinite := BitVec.ofBool pf.isInfinite
  nan := BitVec.ofBool pf.isNaN
  val :=
    let unshifted : BitVec (s+1) :=
      BitVec.cons (!pf.isZeroOrSubnorm) (pf.sig);
    BitVec.shiftLeft (BitVec.zeroExtend _ (unshifted)) (pf.ex.toNat - 1)
  hExOffset := by
    apply Nat.lt_of_le_of_lt (sub_two_lt)
    apply Nat.add_lt_add_right
    exact Nat.two_pow_pred_lt_two_pow he


/-# Contents of File

- @bollu assigns assignment: Setup CI! (done)
- Create a document of this that can be shown to Tobias without shame
- Definitions of PackedFloat and FixedPoint representations (done)
  + Add a sign bit to FixedPoint
- Conversion from PackedFloat to FixedPoint
- (next step: in another file called Fp.FixedPoint, create addition)
- Show floating point addition is commutative
  + Do conversion back to floating point
    * Implement some sort of rounding
    * Implement re-packing FixedPoint -> PackedFloat
  + Implement equality for floating point
  + Implement round-trip rounded floating point addition
  + Prove f1 + f2 = f2 + f1 by asking bv_decide
- Show that fixed -> float conversion is left inverse to float -> fixed ('sorry' for now).
  + Exclude NaN of course
- (@bollu's thought): We may like to have `FixedPoint.toRat : FixedPoint → ℚ`, which
  interprets the FP as a rational.

-/
end PackedFloat

-- Temp playground

def oneE5M2 : PackedFloat 5 2 where
  ex := 15#5
  sig := 0#2
  sign := 0#1

#eval (repr oneE5M2)

def minNormE5M2 : PackedFloat 5 2 where
  ex := 1#5
  sig := 0#2
  sign := 0#1

def minDenormE5M2 : PackedFloat 5 2 where
  ex := 0#5
  sig := 1#2
  sign := 0#1

#check PackedFloat.toFixed
#eval (PackedFloat.nan 5 2)
#eval oneE5M2.toFixed (by omega)
#eval minDenormE5M2.toFixed (by omega)
#eval minNormE5M2.toFixed (by omega)

-- Sanity checks
theorem fixed_of_minDenormE5M2_is_0b1 : (minDenormE5M2.toFixed (by omega)).val.toNat = 1 := by
  rfl

theorem fixed_of_minNormE5M2_is_0b100 : (minNormE5M2.toFixed (by omega)).val.toNat = 4 := by
  rfl
