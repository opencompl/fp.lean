import Fp.Basic
import Fp.Rounding

def f_add (a b : FixedPoint w e) : FixedPoint (w+1) e :=
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
    -- TODO: actually when rounding mode is RTN we should return -0.0
    {
      sign := False
      val := BitVec.zero _
      hExOffset := hExOffset
    }

def e_add (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
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
    num := f_add a.num b.num
  }

def add (he : 0 < e) (a b : PackedFloat e s) : PackedFloat e s :=
  round _ _ (e_add (a.toEFixed he) (b.toEFixed he))

theorem FixedPoint_add_comm' (a b : FixedPoint 16 8)
  : (f_add a b).equal (f_add b a) := by
  simp [f_add]
  bv_decide +acNf

theorem EFixedPoint_add_comm' (a b : EFixedPoint 16 8)
  : (e_add a b).equal_or_nan (e_add b a) := by
  simp [e_add, f_add]
  bv_decide +acNf

theorem PackedFloat_add_comm' (a b : PackedFloat 5 2)
  : (add (by omega) a b) = (add (by omega) b a) := by
  apply PackedFloat.inj
  simp [add, e_add, f_add, round, PackedFloat.toEFixed, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_check "Addition.lean-PackedFloat_add_comm-75-2.lrat"

theorem FixedPoint_add_comm (a b : FixedPoint 34 16)
  : (f_add a b) = (f_add b a) := by
  apply FixedPoint.inj
  simp [f_add]
  bv_decide +acNf

theorem EFixedPoint_add_comm (a b : EFixedPoint 34 16)
  : (e_add a b) = (e_add b a) := by
  simp [e_add]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp <;> simp_all only [eq_comm, FixedPoint_add_comm]

theorem PackedFloat_add_comm (a b : PackedFloat 5 2)
  : (add (by omega) a b) = (add (by omega) b a) := by
  simp [add, EFixedPoint_add_comm]
