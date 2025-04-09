import Fp.Basic
import Lean.Elab.Tactic.BVDecide

def fixedPoint_eq (a b : FixedPoint w e) : Bool :=
  if a.sign != b.sign then
    a.val == BitVec.zero _ && b.val == BitVec.zero _
  else
   a.val == b.val

def fixedPoint_add (a b : FixedPoint w e) : FixedPoint (w+1) e :=
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


def add (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
  open EFixedPoint in
  match a, b with
  | NaN, _
  | _ , NaN => NaN
  | Infinity s, Infinity t =>
    if s = t then Infinity s
    else NaN
  | Infinity s, _
  | _, Infinity s => Infinity s
  | Number a, Number b =>
    EFixedPoint.Number (fixedPoint_add a b)

def test_zero := EFixedPoint.zero 8 16 (by omega)

theorem FixedPoint_eq_refl (a : FixedPoint w e)
  : (fixedPoint_eq a a) = true := by
  simp [fixedPoint_eq]

theorem FixedPoint_add_comm (a b : FixedPoint 16 8)
  : (fixedPoint_add a b) = (fixedPoint_add b a) := by
  simp [fixedPoint_add]
  apply FixedPoint.inj
  bv_decide

theorem FixedPoint_add_comm2 (a b : FixedPoint 16 8)
  : fixedPoint_eq (fixedPoint_add a b) (fixedPoint_add b a) := by
  simp [FixedPoint_add_comm]
  exact FixedPoint_eq_refl _

theorem test : test_zero.equal test_zero = true := by
  simp [test_zero, EFixedPoint.zero, EFixedPoint.equal]

-- TODO: addition of non-NaN fixed point is commutative
theorem EFixedPoint_add_comm (a b : EFixedPoint 16 8)
  (ha : a.isNaN = false) (hb : b.isNaN = false)
  : (add a b).equal (add b a) = true := by
  simp [EFixedPoint.isNaN] at ha hb
  simp [add, EFixedPoint.equal]
  sorry
  --bv_decide


def or_test (a b : Bool) : FixedPoint 16 8 :=
  if a == b then
  { sign := a
    val := BitVec.zero _
    hExOffset := by omega }
  else
  { sign := True
    val := BitVec.zero _
    hExOffset := by omega }

theorem or_test_eq_or (a b : Bool) : (or_test a b).sign = a || b := by
  simp [or_test]
  bv_decide

#version
