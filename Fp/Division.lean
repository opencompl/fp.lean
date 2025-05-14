import Fp.Basic
import Fp.Rounding

def div_numbers (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  let sign := a.sign ^^ b.sign
  let sig_a := BitVec.cons (a.ex ≠ 0) a.sig
  let sig_b := BitVec.cons (b.ex ≠ 0) b.sig
  let div_len := 3*(s+1)
  let unit_pos := 2*(s+1)
  let dividend := (sig_a.setWidth div_len <<< unit_pos)
  let divisor := sig_b.setWidth div_len
  -- Do division, collapse remainder to sticky bit
  let quot_with_sticky := (dividend / divisor) ++ BitVec.ofBool ((dividend % divisor) ≠ 0)
  -- Calculate shifts
  let shiftL := if a.ex > 0 then a.ex - 1 else 0
  let shiftR := if b.ex > 0 then b.ex - 1 else 0
  -- Shift and round
  if shiftL ≥ shiftR then
    let quot_lshift : EFixedPoint (2^e+div_len+1) (unit_pos+1) := {
      state := .Number
      num := {
        sign
        val := quot_with_sticky.setWidth _ <<< (shiftL - shiftR)
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right]
          apply Nat.lt_add_left
          omega
      }
    }
    round _ _ mode quot_lshift
  else
    let quot_rshift : EFixedPoint (2^e+div_len+1) (2^e+unit_pos+1) := {
      state := .Number
      num := {
        sign
        val := (quot_with_sticky.setWidth _ <<< 2^e) >>> (shiftR - shiftL)
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_left]
          omega
      }
    }
    round _ _ mode quot_rshift

def div (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  if a.isNaN ∨ b.isNaN ∨ (a.isInfinite ∧ b.isInfinite) ∨ (a.isZero ∧ b.isZero) then
    PackedFloat.getNaN _ _
  else if a.isInfinite ∨ b.isZero then
    PackedFloat.getInfinity _ _ (a.sign ^^ b.sign)
  else if b.isInfinite then
    { PackedFloat.getZero _ _ with sign := a.sign ^^ b.sign }
  else
    div_numbers a b mode

def div_one_is_id (a : PackedFloat 5 2) (h : ¬a.isNaN)
  : div a oneE5M2 .RTZ = a := by
  apply PackedFloat.inj
  simp at h
  simp [oneE5M2, div, div_numbers, round, BitVec.cons, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem div_self_is_one (a : PackedFloat 5 2)
  (h : ¬a.isNaN ∧ ¬a.isInfinite ∧ ¬a.isZero)
  : (div a a .RTZ) = oneE5M2 := by
  apply PackedFloat.inj
  simp at h
  simp [div, div_numbers, round, BitVec.cons, oneE5M2,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
