import Fp.Basic
import Fp.Addition
import Fp.Negation
import Fp.Comparison
import Fp.Multiplication
import Fp.Rounding

-- Helpers

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

theorem doubleRNE_eq_mul_two (a : PackedFloat 5 2)
  : doubleRNE a = mul twoE5M2 a .RNE := by
  apply PackedFloat.inj
  simp [doubleRNE, mul, round, twoE5M2, BitVec.cons,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem add_neg_self_isZero_or_isNaN (a : PackedFloat 5 2) (m : RoundingMode)
  : (add (by omega) a (neg a) m).isZero ∨ (add (by omega) a (neg a) m).isNaN := by
  simp [add, e_add, f_add, neg, round, PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem e_add_monotone (m : RoundingMode) (a b c : EFixedPoint 34 16)
  (hc : c.state = .Number)
  : e_le a b → e_le (e_add m a c) (e_add m b c) := by
  simp_all [e_add, f_add]
  bv_decide

theorem add_monotone (a b c : PackedFloat 5 2) (m : RoundingMode) (hc : c.isNormOrSubnorm)
  : le a b → le (add (by omega) a c m) (add (by omega) b c m) := by
  intro h
  apply le_of_e_le
  have hc' : (c.toEFixed (by omega)).state = .Number :=
    PackedFloat.isNumber_of_isNormOrSubnorm c hc
  apply e_add_monotone _ _ _ _ hc'
  exact e_le_of_le _ _ h

theorem sterbenz (a b : PackedFloat 5 2)
  (h : le a (doubleRNE b) ∧ le b (doubleRNE a))
  : isExactFloat 5 2 (e_add .RTZ (a.toEFixed (by omega)) ((neg b).toEFixed (by omega)))
  := by
  simp [le, doubleRNE] at h
  simp [e_add, f_add, neg, round, isExactFloat,
    PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem sterbenzFP16 (a b : PackedFloat 5 10)
  (h : le a (doubleRNE b) ∧ le b (doubleRNE a))
  : isExactFloat 5 10 (e_add .RTZ (a.toEFixed (by omega)) ((neg b).toEFixed (by omega)))
  := by
  simp [le, doubleRNE] at h
  simp [e_add, f_add, neg, round, isExactFloat,
    PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
