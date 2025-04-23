import Fp.Utils

/-!
## Packed Floating Point Numbers

This is a test module description
-/
/-
inductive Sign : Type
| Positive : Sign
| Negative : Sign
deriving DecidableEq, Repr
-/

/--
A packed floating point number,
whose exponent and significand width are encoded at the type level.
-/
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit. -/
    sign : Bool
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Significand (mantissa) of the packed float. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr


/--
A fixed point number with specified exponent offset.
-/
structure FixedPoint (width exOffset : Nat) where
    sign : Bool
    val : BitVec width
    hExOffset : exOffset < width
deriving DecidableEq, Repr

-- Concretely, any enum we have must look like a C enum, so we must flatten
-- all our state into a single enum.

inductive State : Type
| NaN : State
| Infinity : State
| Number : State
deriving DecidableEq, Repr

/--
A fixed point number extended with infinity and NaN.
-/
structure EFixedPoint (width exOffset : Nat) where
  state : State
  num : FixedPoint width exOffset
deriving DecidableEq, Repr

namespace PackedFloat
/--
Returns the "canonical" NaN for the given floating point format. For example, the canonical NaN for `exWidth` and `sigWidth` 4 is
`0.1111.1000`.
-/
@[simp]
def getNaN (exWidth sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := False
  ex := BitVec.allOnes exWidth
  sig := BitVec.ofNat sigWidth (2 ^ (sigWidth - 1))

@[simp]
def getInfinity (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign := sign
  ex := BitVec.allOnes exWidth
  sig := 0

@[simp]
def getZero (exWidth sigWidth : Nat)
  : PackedFloat exWidth sigWidth where
  sign := False
  ex := 0
  sig := 0

theorem injEq (a b : PackedFloat e s)
  : (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) = (a = b) := by
  cases a
  cases b
  simp [mk.injEq]

theorem inj (a b : PackedFloat e s)
  : (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) → (a = b) := by
  intro h
  simp_all only [injEq]

@[simp]
def isInfinite (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig == 0

@[simp]
def isNaN (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig != 0

@[simp]
def isZeroOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex == 0

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
  let hExOffset : 2 ^ (e - 1) + s - 2 < 2 ^ e + s := by
      apply Nat.lt_of_le_of_lt (sub_two_lt)
      apply Nat.add_lt_add_right
      exact Nat.two_pow_pred_lt_two_pow he
  if pf.isNaN then {
    state := .NaN
    num := {
      sign := False
      val := 0
      hExOffset
    }
  }
  else if pf.isInfinite then {
    state := .Infinity
    num := {
      sign := pf.sign
      val := 0
      hExOffset
    }
  }
  else {
    state := .Number
    num := {
      sign := pf.sign
      val :=
        let unshifted : BitVec (1+s) :=
          (BitVec.ofBool !pf.isZeroOrSubnorm) ++ pf.sig;
        let shift : BitVec e := if pf.ex = 0 then 0 else pf.ex - 1
        let hs : 1 + s <= 2^e + s := by
          exact Nat.add_le_add_right Nat.one_le_two_pow s
        (BitVec.setWidth' hs (unshifted)) <<< shift
      hExOffset
    }
  }

def getValOrNone (pf : PackedFloat e s) (he : 0 < e)
  : Option Nat :=
  let result := toEFixed pf he
  match result.state with
  | .NaN | .Infinity => none
  | .Number => some result.num.val.toNat

end PackedFloat

namespace FixedPoint
@[simp]
def equal (a b : FixedPoint w e) : Bool :=
  (a.val == BitVec.zero _ && b.val == BitVec.zero _)
  || (a.sign == b.sign && a.val == b.val)

theorem injEq (a b : FixedPoint w e)
  : (a.sign = b.sign ∧ a.val = b.val) = (a = b) := by
  cases a
  cases b
  simp only [mk.injEq]

theorem inj (a b : FixedPoint w e)
  : (a.sign = b.sign ∧ a.val = b.val) → (a = b) := by
  intro h
  simp_all only [injEq]

theorem equal_refl (a : FixedPoint w e)
  : (a.equal a) = true := by
  simp [FixedPoint.equal]

theorem equal_comm (a b : FixedPoint w e)
  : (a.equal b) = (b.equal a) := by
  simp [equal, Bool.beq_comm]
  ac_nf

end FixedPoint

namespace EFixedPoint
theorem injEq (a b : EFixedPoint w e)
  : (a.state = b.state ∧ a.num.sign = b.num.sign ∧ a.num.val = b.num.val)
      = (a = b) := by
  cases a
  cases b
  simp only [FixedPoint.injEq, mk.injEq]

theorem inj (a b : EFixedPoint w e)
  : (a.state = b.state ∧ a.num.sign = b.num.sign ∧ a.num.val = b.num.val)
      → (a = b) := by
  intro h
  simp_all only [injEq]

@[simp]
def getNaN (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .NaN
  num := {
    sign := False
    val := 0
    hExOffset
  }

@[simp]
def getInfinity (sign : Bool) (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Infinity
  num := {
    sign
    val := 0
    hExOffset
  }

@[simp]
def zero (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Number
  num := {
    sign := False
    val := 0
    hExOffset
  }

@[simp]
def equal (a b : EFixedPoint w e) : Bool :=
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number && a.num.equal b.num)

@[simp]
def equal_or_nan (a b : EFixedPoint w e) : Bool :=
  a.state = .NaN || b.state = .NaN || a.equal b

@[simp]
def isNaN (a : EFixedPoint w e) : Bool :=
  a.state == .NaN

end EFixedPoint

-- Temp playground

def oneE5M2 : PackedFloat 5 2 where
  ex := 15#5
  sig := 0#2
  sign := False

#eval (repr oneE5M2)

def minNormE5M2 : PackedFloat 5 2 where
  ex := 1#5
  sig := 0#2
  sign := False

def minDenormE5M2 : PackedFloat 5 2 where
  ex := 0#5
  sig := 1#2
  sign := False

#check PackedFloat.toEFixed
#eval (PackedFloat.getNaN 5 2)
#eval oneE5M2.toEFixed (by omega)
#eval minDenormE5M2.toEFixed (by omega)
#eval minNormE5M2.toEFixed (by omega)

-- Sanity checks
theorem fixed_of_minDenormE5M2_is_0b1
  : PackedFloat.getValOrNone minDenormE5M2 (by omega) = some 1 := by
  simp [minDenormE5M2, PackedFloat.getValOrNone,
        PackedFloat.toEFixed]

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
