import Fp.Utils

/-!
## Packed Floating Point Numbers

This is a test module description
-/

inductive Sign : Type
| Positive : Sign
| Negative : Sign
deriving DecidableEq, Repr

/--
A packed floating point number,
whose exponent and significand width are encoded at the type level.
-/
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit. -/
    sign : Sign
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Significand (mantissa) of the packed float. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr


/--
A fixed point number with specified exponent offset.
-/
structure FixedPoint (width exOffset : Nat) where
    sign : Sign
    val : BitVec width
    hExOffset : exOffset < width
deriving DecidableEq, Repr

/--
A fixed point number extended with infinity and NaN.
-/
inductive EFixedPoint (width exOffset : Nat) : Type
| NaN : EFixedPoint width exOffset
| Infinity : Sign -> EFixedPoint width exOffset
| Number : FixedPoint width exOffset -> EFixedPoint width exOffset
deriving DecidableEq, Repr

namespace PackedFloat
/--
Returns the "canonical" NaN for the given floating point format. For example, the canonical NaN for `exWidth` and `sigWidth` 4 is
`0.1111.1000`.
-/
def getNaN (exWidth sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := Sign.Positive
  ex := BitVec.allOnes exWidth
  sig := BitVec.ofNat sigWidth (2 ^ (sigWidth - 1))

def getInfinity (exWidth sigWidth : Nat) (sign : Sign)
  : PackedFloat exWidth sigWidth where
  sign := sign
  ex := BitVec.allOnes exWidth
  sig := BitVec.zero sigWidth

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
def toEFixed (pf : PackedFloat e s) (he : 0 < e)
  : EFixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2) :=
  if pf.isNaN then EFixedPoint.NaN
  else if pf.isInfinite then EFixedPoint.Infinity pf.sign
  else EFixedPoint.Number {
    sign := pf.sign
    val :=
      let unshifted : BitVec (s+1) :=
        BitVec.cons (!pf.isZeroOrSubnorm) (pf.sig);
      let hS : s + 1 <= 2^e + s := by
        rewrite [Nat.add_comm]
        apply Nat.add_le_add_right Nat.one_le_two_pow s
      BitVec.shiftLeft (BitVec.setWidth' hS (unshifted)) (pf.ex.toNat - 1)
    hExOffset := by
      apply Nat.lt_of_le_of_lt (sub_two_lt)
      apply Nat.add_lt_add_right
      exact Nat.two_pow_pred_lt_two_pow he
  }

def getValOrNone (pf : PackedFloat e s) (he : 0 < e)
  : Option Nat :=
  match toEFixed pf he with
  | EFixedPoint.NaN => none
  | EFixedPoint.Infinity _ => none
  | EFixedPoint.Number f => some f.val.toNat

end PackedFloat

namespace EFixedPoint

def zero (sigWidth exWidth : Nat) (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth :=
  EFixedPoint.Number {
    sign := Sign.Positive
    val := BitVec.zero _
    hExOffset := hExOffset
  }

def equal (a b : EFixedPoint w e) : Bool :=
  match a, b with
  | Infinity s1, Infinity s2 => s1 = s2
  | Number a, Number b =>
    (a.val == 0 && b.val == 0) || (a.sign == b.sign && a.val == b.val)
  | _, _ => false

def isNaN : EFixedPoint w e → Bool
  | NaN => true | _ => false

end EFixedPoint

-- Temp playground

def oneE5M2 : PackedFloat 5 2 where
  ex := 15#5
  sig := 0#2
  sign := Sign.Positive

#eval (repr oneE5M2)

def minNormE5M2 : PackedFloat 5 2 where
  ex := 1#5
  sig := 0#2
  sign := Sign.Positive

def minDenormE5M2 : PackedFloat 5 2 where
  ex := 0#5
  sig := 1#2
  sign := Sign.Positive

#check PackedFloat.toEFixed
#eval (PackedFloat.getNaN 5 2)
#eval oneE5M2.toEFixed (by omega)
#eval minDenormE5M2.toEFixed (by omega)
#eval minNormE5M2.toEFixed (by omega)

-- Sanity checks
theorem fixed_of_minDenormE5M2_is_0b1
  : PackedFloat.getValOrNone minDenormE5M2 (by omega) = some 1 := by
  simp [minDenormE5M2, PackedFloat.getValOrNone,
        PackedFloat.toEFixed, PackedFloat.isNaN, PackedFloat.isInfinite,
        PackedFloat.isZeroOrSubnorm]

theorem fixed_of_minNormE5M2_is_0b100
  : PackedFloat.getValOrNone minNormE5M2 (by omega) = some 4 := by
  rfl


/-
# To-do list

- @bollu assigns assignment: Setup CI! (done)
- Create a document of this that can be shown to Tobias without shame
- Definitions of PackedFloat and FixedPoint representations (done)
  + Add a sign bit to FixedPoint
- Conversion from PackedFloat to FixedPoint (done, mostly)
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
