import Fp.Basic
import Fp.Rounding

/-- Negate the fixed point number -/
def f_neg (a : FixedPoint w e) : FixedPoint w e := { a with sign := !a.sign }

/-- Negate the extended fixed point number -/
def e_neg (a : EFixedPoint w e) : EFixedPoint w e :=
  open EFixedPoint in
  have := a.num.hExOffset
  if hN : a.state = .NaN then
    getNaN (by omega)
  else if hInf : a.state = .Infinity then
    getInfinity (!a.num.sign) (by omega)
  else
    let _ : a.state = .Number := by
      cases h : a.state <;> simp_all
    { a with num := f_neg a.num }

/-- Negate a floating-point number, by conversion to a fixed-point number. -/
def negfixed (a : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  round _ _ mode (e_neg a.toEFixed)

/--
Negate a floating-point number, by flipping the sign bit.

This implements the same function as `negfixed`, but is much simpler.
-/
def neg (a : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN then PackedFloat.getNaN _ _
  else { a with sign := !a.sign }

theorem f_neg_involutive (a : FixedPoint 16 8)
  : f_neg (f_neg a) = a := by
  simp [f_neg]

theorem e_neg_involutive (a : EFixedPoint 16 8)
  : (e_neg (e_neg a)).equal_denotation a := by
  simp [e_neg, f_neg, EFixedPoint.equal_denotation]
  bv_decide

/--
`negfixed` and `neg` implement the same function.
-/
theorem negfixed_eq_neg (a : PackedFloat 5 2) (m : RoundingMode)
  : negfixed a m = neg a := by
  apply PackedFloat.inj
  simp [negfixed, neg, e_neg, f_neg, round, PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

/--
Applying `neg` twice gives you the identity.
-/
theorem neg_involutive (a : PackedFloat e s) (h : ¬a.isNaN)
  : neg (neg a) = a := by
  have h' : ¬(neg a).isNaN := by
    unfold neg
    simp only [h]
    simp_all
  unfold neg at h' ⊢
  simp only [h', h]
  simp_all
