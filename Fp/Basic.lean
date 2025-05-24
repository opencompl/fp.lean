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

instance : Repr (PackedFloat exWidth sigWidth) where
  reprPrec x _prec :=
    f!"\{ sign := {if x.sign then "-" else "+"}, ex := {x.ex}, sig := {x.sig} }"


/--
A fixed point number with specified exponent offset.
-/
structure FixedPoint (width exOffset : Nat) where
    sign : Bool
    val : BitVec width
    hExOffset : exOffset < width
deriving DecidableEq

instance : Repr (FixedPoint width ExOffset) where
  reprPrec (x : FixedPoint _ _) _prec :=
    f!"{if x.sign then "-" else "+"} {x.val}"

-- Concretely, any enum we have must look like a C enum, so we must flatten
-- all our state into a single enum.

/--
The "state" of an extended fixed-point number: either NaN, infinity, or a
number.
-/
inductive State : Type
| NaN : State
| Infinity : State
| Number : State
deriving DecidableEq

instance : Repr State where
  reprPrec s _prec :=
    match s with
    | .NaN => "NaN"
    | .Infinity => "∞"
    | .Number => "num"

/--
A fixed point number extended with infinity and NaN.
-/
structure EFixedPoint (width exOffset : Nat) where
  state : State
  num : FixedPoint width exOffset
deriving DecidableEq, Repr

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

/--
Floating point equality test.
Recall that `NaN ≠ Nan` under the floating point semantics.
-/
@[simp]
def equal (a b : EFixedPoint w e) : Bool :=
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number && a.num.equal b.num)

@[simp]
def equal_or_nan (a b : EFixedPoint w e) : Bool :=
  a.state = .NaN || b.state = .NaN || a.equal b

/--
Floating point equality test,
where we check upto denotation. So, under this definition:
- NaN = Nan iff the states are both Nan.
- +Infinity = +Infinity, -Infinity = -Infinity.
- Number equality is reflexive.
-/
@[simp]
def equal_denotation (a b : EFixedPoint w e) : Bool :=
  (a.state = .NaN && b.state = .NaN) ||
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number && a.num.equal b.num)

@[simp]
def isNaN (a : EFixedPoint w e) : Bool :=
  a.state = .NaN

@[simp]
def isZero (a : EFixedPoint w e) : Bool :=
  a.state = .Number && a.num.val == 0

end EFixedPoint

namespace PackedFloat

/--
Returns the "canonical" NaN for the given floating point format. For example,
the canonical NaN for `exWidth = 3` and `sigWidth = 4` is `0.111.1000`.
-/
@[simp]
def getNaN (exWidth sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := False
  ex := BitVec.allOnes exWidth
  sig := BitVec.ofNat sigWidth (2 ^ (sigWidth - 1))

/--
Returns the infinity value of the specified sign for the given floating point
format.
-/
@[simp]
def getInfinity (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth
  sig := 0

/--
Returns the (positive) zero value for the given floating point format.
-/
@[simp]
def getZero (exWidth sigWidth : Nat)
  : PackedFloat exWidth sigWidth where
  sign := False
  ex := 0
  sig := 0

/--
Returns the maximum (magnitude) value for the given sign.
-/
@[simp]
def getMax (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth - 1
  sig := BitVec.allOnes sigWidth

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
def isNormOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex != BitVec.allOnes e

@[simp]
def isZeroOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex == 0

@[simp]
def isZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0

/--
Returns the `PackedFloat` representation for the given `BitVec`.
-/
@[simp]
def ofBits (e s : Nat) (b : BitVec (1+e+s)) : PackedFloat e s where
  sign := b.msb
  ex := (b >>> s).truncate e
  sig := b.truncate s

/--
Returns the `BitVec` representation for the given `PackedFloat`.
-/
@[simp]
def toBits (x : PackedFloat e s) : BitVec (1+e+s) :=
  BitVec.ofBool x.sign ++ x.ex ++ x.sig

/--
Convert from a packed float to a fixed point number.

Conversion function assumes IEEE compliance. For output `FixedPoint` number to
have a non-degenerate exponent offset, we need two or more bits in the
exponent.

NOTE: Assuming IEEE compliance, you technically only need 2^e + s - 2 bits to
cover the entire range of representable values.
-/
def toEFixed (pf : PackedFloat e s)
  : EFixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2) :=
  let hExOffset := toEFixed_hExOffset
  if pf.isNaN then EFixedPoint.getNaN hExOffset
  else if pf.isInfinite then EFixedPoint.getInfinity pf.sign hExOffset
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

theorem isNumber_of_isNormOrSubnorm (a : PackedFloat e s)
  : a.isNormOrSubnorm → a.toEFixed.state = .Number := by
  simp_all [toEFixed]

end PackedFloat

-- Constants

/-- E5M2 floating point representation of 1.0 -/
def oneE5M2       := PackedFloat.ofBits 5 2 0b00111100#8
/-- E5M2 floating point representation of 2.0 -/
def twoE5M2       := PackedFloat.ofBits 5 2 0b01000000#8
/-- Smallest (positive) normal number in E5M2 floating point. -/
def minNormE5M2   := PackedFloat.ofBits 5 2 0b00000100#8
/-- Smallest (positive) subnormal number in E5M2 floating point. -/
def minSubnormE5M2 := PackedFloat.ofBits 5 2 0b00000001#8

/-- info: { sign := +, ex := 0x0f#5, sig := 0x0#2 } -/
#guard_msgs in #eval (repr oneE5M2)
/-- info: { sign := +, ex := 0x1f#5, sig := 0x2#2 } -/
#guard_msgs in #eval (PackedFloat.getNaN 5 2)
/-- info: { state := num, num := + 0x000010000#34 } -/
#guard_msgs in #eval oneE5M2.toEFixed
/-- info: { state := num, num := + 0x000000001#34 } -/
#guard_msgs in #eval minSubnormE5M2.toEFixed
/-- info: { state := num, num := + 0x000000004#34 } -/
#guard_msgs in #eval minNormE5M2.toEFixed

/-
- (@bollu's thought): We may like to have `FixedPoint.toRat : FixedPoint → ℚ`, which
  interprets the FP as a rational.
-/
