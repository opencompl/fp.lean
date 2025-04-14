import Fp.Basic
import Lean.Elab.Tactic.BVDecide

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

theorem FixedPoint_add_comm (a b : FixedPoint 16 8)
  : (f_add a b).equal (f_add b a) := by
  simp [f_add, FixedPoint.equal]
  bv_decide

theorem EFixedPoint_add_comm (a b : EFixedPoint 16 8)
  : (e_add a b).equal_or_nan (e_add b a) := by
  open EFixedPoint in
  simp [e_add, equal_or_nan, equal, getNaN, getInfinity,
        f_add, FixedPoint.equal]
  bv_decide
