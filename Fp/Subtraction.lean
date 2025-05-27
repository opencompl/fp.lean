import Fp.Basic
import Fp.Rounding
import Fp.Addition
import Fp.Negation

/--
Subtraction of two extended fixed-point numbers.
-/
def e_sub (mode : RoundingMode) (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
  e_add mode a (e_neg b)

/--
Subtraction of two floating-point numbers.

Implemented entirely within EFixedPoint using `e_sub`.
-/
def subfixed (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  round _ _ mode (e_sub mode a.toEFixed b.toEFixed)

/--
Subtraction of two floating-point numbers.

Implemented as a negation followed by an addition.
-/
def sub (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  add a (neg b) mode

theorem subfixed_eq_sub (a b : PackedFloat 5 2) (m : RoundingMode)
  : subfixed a b m = sub a b m := by
  apply PackedFloat.inj
  simp [subfixed, sub, add, neg, e_sub, e_add, f_add, e_neg, f_neg,
    round, PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
