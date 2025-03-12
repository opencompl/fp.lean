import Fp.Basic

def add (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
  open EFixedPoint in
  match a, b with
  | NaN, _ => NaN
  | _ , NaN => NaN
  | Infinity s, Infinity t =>
    if s = t then Infinity s
    else NaN
  | Infinity s, _
  | _, Infinity s => Infinity s
  | Number a, Number b =>
    let hExOffset : e < w+1 := by
      exact Nat.lt_add_right 1 a.hExOffset
    let ax := BitVec.zeroExtend _ a.val
    let bx := BitVec.zeroExtend _ b.val
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
