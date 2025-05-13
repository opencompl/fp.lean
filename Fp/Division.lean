import Fp.Basic
import Fp.Rounding

def div_numbers (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  let sign := a.sign ^^ b.sign
  let sig_a := BitVec.cons (a.ex ≠ 0) a.sig
  let sig_b := BitVec.cons (b.ex ≠ 0) b.sig
  let div_len := 3*(s+1)
  let unit_pos := 2*(s+1)
  -- Do division, collapse remainder to sticky bit
  let div_res := BitVec.divRec div_len {
    n := sig_a.setWidth _ <<< unit_pos
    d := sig_b.setWidth _
  } (BitVec.DivModState.init div_len)
  let quot_with_sticky := div_res.q ++ BitVec.ofBool (div_res.r ≠ 0)
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

-- This theorem is hella broken right now.
set_option maxHeartbeats 200000
def div_one_is_id (a : PackedFloat 5 2)
  : div a oneE5M2 .RTZ = a := by
  apply PackedFloat.inj
  simp [oneE5M2, div, div_numbers, round, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  unfold BitVec.divSubtractShift
--  bv_decide
  sorry
