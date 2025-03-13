import Fp.Basic
import Lean.Elab.Tactic.BVDecide

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
    let hExOffset : e < w+1 := by
      exact Nat.lt_add_right 1 a.hExOffset
    let ax := BitVec.setWidth' (by omega) a.val
    let bx := BitVec.setWidth' (by omega) b.val
    if a.sign == b.sign then
      -- Addition of same-signed numbers always preserves sign
      EFixedPoint.Number {
        sign := a.sign
        val := BitVec.add ax bx
        hExOffset := hExOffset
      }
    else if BitVec.ult ax bx then
      EFixedPoint.Number {
        sign := b.sign
        val := BitVec.sub bx ax
        hExOffset := hExOffset
      }
    else if BitVec.ult bx ax then
      EFixedPoint.Number {
        sign := a.sign
        val := BitVec.sub ax bx
        hExOffset := hExOffset
      }
    else
      -- Signs are different but values are same, so return +0.0
      EFixedPoint.zero _ _ hExOffset

def test_zero := EFixedPoint.zero 8 16 (by omega)

theorem test : test_zero.equal test_zero = true := by
  simp [test_zero, EFixedPoint.zero, EFixedPoint.equal]

theorem EFixedPoint_eq_refl (a : EFixedPoint 16 8) (ha : a.isNaN = false)
  : a.equal a = true := by
  cases a
  simp [EFixedPoint.isNaN] at ha
  simp [EFixedPoint.equal]
  sorry
  --bv_decide

-- TODO: addition of non-NaN fixed point is commutative
theorem EFixedPoint_add_comm (a b : EFixedPoint 16 8)
  (ha : a.isNaN = false) (hb : b.isNaN = false)
  : (add a b).equal (add b a) = true := by
  simp [add, EFixedPoint.isNaN, EFixedPoint.equal]
  sorry
  --bv_decide
