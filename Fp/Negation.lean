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
    { a with num := f_neg a.num }

def neg (he : 0 < e) (a : PackedFloat e s) : PackedFloat e s :=
  round _ _ (e_neg (a.toEFixed he))

theorem FixedPoint_neg_involutive (a : FixedPoint 16 8)
  : f_neg (f_neg a) = a := by
  simp [f_neg]

theorem EFixedPoint_neg_involutive (a : EFixedPoint 16 8)
  : (e_neg (e_neg a)).equal_denotation a := by
  simp [e_neg, f_neg, EFixedPoint.equal_denotation]
  bv_decide

