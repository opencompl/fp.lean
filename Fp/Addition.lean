import Fp.Basic
import Fp.Rounding

def f_add (mode : RoundingMode) (a b : FixedPoint w e) : FixedPoint (w+1) e :=
  let hExOffset : e < w+1 := by
    exact Nat.lt_add_right 1 a.hExOffset
  let ax := BitVec.setWidth' (by omega) a.val
  let bx := BitVec.setWidth' (by omega) b.val
  if a.sign == b.sign then
    -- Addition of same-signed numbers always preserves sign
    {
      sign := a.sign
      val := BitVec.add ax bx
      hExOffset := hExOffset
    }
  else if BitVec.ult ax bx then
    {
      sign := b.sign
      val := BitVec.sub bx ax
      hExOffset := hExOffset
    }
  else if BitVec.ult bx ax then
    {
      sign := a.sign
      val := BitVec.sub ax bx
      hExOffset := hExOffset
    }
  else
    -- Signs are different but values are same, so return +0.0
    -- When rounding mode is RTN we should instead return -0.0
    {
      sign := mode == .RTN
      val := BitVec.zero _
      hExOffset := hExOffset
    }

def e_add (mode : RoundingMode) (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
  open EFixedPoint in
  let hExOffset : e < w + 1 := by
    exact Nat.lt_add_right 1 a.num.hExOffset
  -- As of 2025-04-14, bv_decide does not support pattern matches on more than
  -- one variable, so we'll have to deal with if-statements for now
  if hN : a.state = .NaN || b.state = .NaN then getNaN hExOffset
  else if hI1 : a.state = .Infinity && b.state = .Infinity then
    if a.num.sign == b.num.sign then getInfinity a.num.sign hExOffset
    else getNaN hExOffset
  else if hI2 : a.state = .Infinity then getInfinity a.num.sign hExOffset
  else if hI3 : b.state = .Infinity then getInfinity b.num.sign hExOffset
  else
  -- is this how to do assertions?
  let _ : a.state = .Number && b.state = .Number := by
    cases ha : a.state <;> cases hb : b.state <;> simp_all
  {
    state := .Number
    num := f_add mode a.num b.num
  }

def add (he : 0 < e) (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  round _ _ mode (e_add mode (a.toEFixed he) (b.toEFixed he))

-- Proof by brute force (it takes a while)
/-
theorem PackedFloat_add_comm' (m : RoundingMode) (a b : PackedFloat 5 2)
  : (add (by omega) a b m) = (add (by omega) b a m) := by
  apply PackedFloat.inj
  simp [add, e_add, f_add, round, PackedFloat.toEFixed, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
-/

theorem f_add_comm (m : RoundingMode) (a b : FixedPoint 34 16)
  : (f_add m a b) = (f_add m b a) := by
  apply FixedPoint.inj
  simp [f_add]
  bv_decide +acNf

theorem e_add_comm (m : RoundingMode) (a b : EFixedPoint 34 16)
  : (e_add m a b) = (e_add m b a) := by
  simp [e_add]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp <;> simp_all only [eq_comm, f_add_comm]

theorem add_comm (m : RoundingMode) (a b : PackedFloat 5 2)
  : (add (by omega) a b m) = (add (by omega) b a m) := by
  simp [add, e_add_comm]

/-- info: { sign := +, ex := 0x04#5, sig := 0x0#2 } -/
#guard_msgs in #eval add (by omega) (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8) .RNE
/-- info: { sign := +, ex := 0x04#5, sig := 0x1#2 } -/
#guard_msgs in #eval add (by omega) (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8) .RNA
