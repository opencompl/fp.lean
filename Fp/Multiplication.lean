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

def mulfixed
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

theorem mulfixed_comm (a b : PackedFloat 5 2) (m : RoundingMode)
  : (mulfixed (by omega) a b m) = (mulfixed (by omega) b a m) := by
  simp [mulfixed, e_mul_comm]

-- A bit-blastable version of multiplication, unrelated to fixed-point numbers
def mul
  (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  if a.isNaN || b.isNaN ||
    (a.isInfinite && b.isZero) ||
    (b.isInfinite && a.isZero) then PackedFloat.getNaN _ _
  else if a.isInfinite || b.isInfinite then
    PackedFloat.getInfinity _ _ (a.sign ^^ b.sign)
  else
    let sa := BitVec.cons (a.ex != 0) a.sig
    let sb := BitVec.cons (b.ex != 0) b.sig
    let shift : BitVec (e+1) :=
      (if a.ex == 0 then 0 else a.ex - 1).setWidth _ +
      (if b.ex == 0 then 0 else b.ex - 1).setWidth _
    let prod := sa.setWidth (2*(s+1)) * sb.setWidth (2*(s+1))
    let result : EFixedPoint (2*2^e + 2*(s+1)) (2^e + 2*s - 4) :=
      {
        state := .Number
        num := {
          sign := a.sign ^^ b.sign
          val := prod.setWidth _ <<< shift
          hExOffset := by omega
        }
      }
    round _ _ m result

theorem mul_comm (a b : PackedFloat 5 2) (m : RoundingMode)
  : (mul a b m) = (mul b a m) := by
  apply PackedFloat.inj
  simp [mul, round, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem mul_one_is_id (a : PackedFloat 5 2) (m : RoundingMode) (ha : ¬a.isNaN)
  : (mul a Tests.oneE5M2 m) = a := by
  apply PackedFloat.inj
  simp at ha
  simp [mul, round, BitVec.cons, Tests.oneE5M2, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
