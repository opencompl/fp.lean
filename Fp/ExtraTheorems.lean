import Fp.Basic
import Fp.Addition
import Fp.Negation
import Fp.Comparison
import Fp.Multiplication
import Fp.Rounding

-- Helpers

def twoE5M2 : PackedFloat 5 2 := PackedFloat.ofBits _ _ 0b01000000

/-- Doubles the given floating point number, rounding to nearest if applicable. -/
def doubleRNE (a : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN then PackedFloat.getNaN _ _
  else if a.isZeroOrSubnorm then
    let ex := if a.sig.msb then 1 else 0
    { sign := a.sign, ex, sig := a.sig <<< 1 }
  else
    let ex := if a.ex == BitVec.allOnes _ then BitVec.allOnes _ else a.ex + 1
    let sig := if ex == BitVec.allOnes _ then 0 else a.sig
    { sign := a.sign, ex, sig }

-- Theorems

theorem add_eq_mul_two (a : PackedFloat 5 2) (m : RoundingMode)
  : add (by omega) a a m = mul twoE5M2 a m := by
  apply PackedFloat.inj
  simp [add, e_add, f_add, twoE5M2, mul, round,
    PackedFloat.toEFixed, BitVec.cons,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem doubleRNE_eq_times_two (a : PackedFloat 5 2)
  : doubleRNE a = mul twoE5M2 a .RNE := by
  apply PackedFloat.inj
  simp [doubleRNE, mul, round, twoE5M2, BitVec.cons,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem sterbenz (a b : PackedFloat 5 2)
  (hc : a ≠ b)
  (h : le a (doubleRNE b) ∧ le b (doubleRNE a))
  : add (by omega) a (neg b) .RTN = add (by omega) a (neg b) .RTP
  := by
    apply PackedFloat.inj
    simp [le, doubleRNE] at h
    simp [← PackedFloat.injEq] at hc
    simp [add, e_add, f_add, neg, round,
      PackedFloat.toEFixed,
      -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
    bv_decide
