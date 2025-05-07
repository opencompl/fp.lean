import Fp.Basic
import Fp.Rounding

def f_mul (a : FixedPoint v e) (b : FixedPoint w f) : FixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.hExOffset b.hExOffset
  let a' : BitVec (v+w) := a.val.setWidth' (by omega)
  let b' : BitVec (v+w) := b.val.setWidth' (by omega)
  {
    sign := a.sign ^^ b.sign
    val := a' * b'
    hExOffset
  }

def e_mul (a : EFixedPoint v e) (b : EFixedPoint w f) : EFixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.num.hExOffset b.num.hExOffset
  open EFixedPoint in
  if hN : a.state = .NaN || b.state = .NaN ||
      (a.state = .Infinity && b.isZero) ||
      (b.state = .Infinity && a.isZero) then getNaN hExOffset
  else if hI1 : a.state = .Infinity || b.state = .Infinity then
    getInfinity (a.num.sign ^^ b.num.sign) hExOffset
  else
    let _ : a.state = .Number && b.state = .Number := by
      cases ha : a.state <;> cases hb : b.state <;> simp_all
    {
      state := .Number
      num := f_mul a.num b.num
    }

def mul
  (he : 0 < e) (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  round _ _ m (e_mul (a.toEFixed he) (b.toEFixed he))

-- Bitblasting multiplication is a bit too hard, so we'll prove these theorems
-- manually
theorem f_mul_comm (a b : FixedPoint 34 16)
  : (f_mul a b) = (f_mul b a) := by
  simp [f_mul, Bool.xor_comm, BitVec.mul_comm]

theorem e_mul_comm (a b : EFixedPoint 34 16)
  : (e_mul a b) = (e_mul b a) := by
  simp [e_mul]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp_all [Bool.xor_comm, f_mul_comm]

theorem mul_comm_brute (a b : EFixedPoint 4 2)
  : (e_mul a b) = (e_mul b a) := by
  apply EFixedPoint.inj
  simp [e_mul, f_mul]
  bv_decide +acNf

theorem mul_comm (a b : PackedFloat 5 2) (m : RoundingMode)
  : (mul (by omega) a b m) = (mul (by omega) b a m) := by
  simp [mul, e_mul_comm]
