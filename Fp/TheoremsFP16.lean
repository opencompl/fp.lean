import Fp.Basic
import Fp.Rounding
import Fp.Addition
import Fp.Negation
import Fp.Division
import Fp.Multiplication
import Fp.Comparison

-- Test file to see how many of the FP8 theorems can be proven on FP16.

def oneE5M10 := PackedFloat.ofBits 5 10 0b0011110000000000#16
def twoE5M10 := PackedFloat.ofBits 5 10 0b0100000000000000#16

-- Comparison

theorem FP16_e_lt_of_lt (a b : PackedFloat 5 10)
  : lt a b ↔ e_lt (a.toEFixed (by omega)) (b.toEFixed (by omega)) := by
  simp [PackedFloat.toEFixed]
  bv_decide

theorem FP16_le_of_e_le (m : RoundingMode) (a b : EFixedPoint 43 24)
  : e_le a b → le (round 5 10 m a) (round 5 10 m b) := by
  simp [round, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem FP16_e_le_of_le (a b : PackedFloat 5 10)
  : le a b → e_le (a.toEFixed (by omega)) (b.toEFixed (by omega)) := by
  simp [PackedFloat.toEFixed]
  bv_decide

-- Rounding

/--
Every floating point number converted to fixed point form, is an exact
floating point number.
-/
theorem FP16_toEFixed_isExactFloat (a : PackedFloat 5 10)
  : isExactFloat 5 10 (a.toEFixed (by omega)) := by
  simp [isExactFloat, PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

/--
If a fixed point number is an exact floating point number, then converting to
floating point and back should not change the denotation.
-/
theorem FP16_isExactFloat_round_toEFixed (a : EFixedPoint 42 24) (m : RoundingMode)
  (ha : isExactFloat 5 10 a)
  : a.equal_denotation ((round 5 10 m a).toEFixed (by omega)) := by
  simp [isExactFloat, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq'] at ha
  simp [PackedFloat.toEFixed, round,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

/-- Fixed -> Float rounding is left inverse to Float -> Fixed conversion -/
theorem FP16_round_leftinv_toEFixed (x : PackedFloat 5 10) (mode : RoundingMode) (hx : ¬ x.isNaN):
  (round _ _ mode (x.toEFixed (by omega))) = x := by
  apply PackedFloat.inj
  simp at hx
  simp [round, PackedFloat.toEFixed, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

-- Addition

theorem FP16_f_add_comm (m : RoundingMode) (a b : FixedPoint 42 24)
  : (f_add m a b) = (f_add m b a) := by
  apply FixedPoint.inj
  simp [f_add]
  bv_decide +acNf

theorem FP16_e_add_comm (m : RoundingMode) (a b : EFixedPoint 42 24)
  : (e_add m a b) = (e_add m b a) := by
  simp [e_add]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp <;> simp_all only [eq_comm, FP16_f_add_comm]

theorem FP16_add_comm (m : RoundingMode) (a b : PackedFloat 5 10)
  : (add (by omega) a b m) = (add (by omega) b a m) := by
  simp [add, FP16_e_add_comm]

theorem FP16_add_neg_self_isZero_or_isNaN (a : PackedFloat 5 10) (m : RoundingMode)
  : (add (by omega) a (neg a) m).isZero ∨ (add (by omega) a (neg a) m).isNaN := by
  simp [add, e_add, f_add, neg, round, PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem FP16_add_zero_is_id (a : PackedFloat 5 10) (m : RoundingMode)
  (ha : ¬a.isNaN ∧ ¬a.isZero)
  : (add (by omega) a (PackedFloat.getZero _ _) m) = a := by
  apply PackedFloat.inj
  simp at ha
  simp [add, e_add, f_add, round, PackedFloat.toEFixed,
      -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem FP16_e_add_monotone (m : RoundingMode) (a b c : EFixedPoint 42 24)
  (hc : c.state = .Number)
  : e_le a b → e_le (e_add m a c) (e_add m b c) := by
  simp_all [e_add, f_add]
  bv_decide

theorem FP16_add_monotone (a b c : PackedFloat 5 10) (m : RoundingMode) (hc : c.isNormOrSubnorm)
  : le a b → le (add (by omega) a c m) (add (by omega) b c m) := by
  intro h
  apply FP16_le_of_e_le
  have hc' : (c.toEFixed (by omega)).state = .Number :=
    PackedFloat.isNumber_of_isNormOrSubnorm c hc
  apply FP16_e_add_monotone _ _ _ _ hc'
  exact FP16_e_le_of_le _ _ h

/--
# Sterbenz Lemma

A floating-point subtraction is computed exactly iff the
operands are within a factor of two of each other.

* <https://en.wikipedia.org/wiki/Sterbenz_lemma>
-/
theorem FP16_sterbenz (a b : PackedFloat 5 10)
  (h : le a (doubleRNE b) ∧ le b (doubleRNE a))
  : isExactFloat 5 10 (e_add .RTZ (a.toEFixed (by omega)) ((neg b).toEFixed (by omega)))
  := by
  simp [le, doubleRNE] at h
  simp [e_add, f_add, neg, round, isExactFloat,
    PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

-- Multiplication

/-- NOTE: bv_decide SAT solver times out on this theorem. -/
theorem FP16_mul_comm (a b : PackedFloat 5 10) (m : RoundingMode)
  : (mul a b m) = (mul b a m) := by
  apply PackedFloat.inj
  simp [mul, round, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  sorry

theorem FP16_mul_one_is_id (a : PackedFloat 5 10) (m : RoundingMode) (ha : ¬a.isNaN)
  : (mul a oneE5M10 m) = a := by
  apply PackedFloat.inj
  simp at ha
  simp [mul, round, BitVec.cons, oneE5M10, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem FP16_add_eq_mul_two (a : PackedFloat 5 10) (m : RoundingMode)
  : add (by omega) a a m = mul twoE5M10 a m := by
  apply PackedFloat.inj
  simp [add, e_add, f_add, twoE5M10, mul, round,
    PackedFloat.toEFixed, BitVec.cons,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem FP16_doubleRNE_eq_mul_two (a : PackedFloat 5 10)
  : doubleRNE a = mul twoE5M10 a .RNE := by
  apply PackedFloat.inj
  simp [doubleRNE, mul, round, twoE5M10, BitVec.cons,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

-- Fixed-point multiplication
-- Bitblasting this is a bit too hard, so we'll prove these theorems manually

theorem FP16_f_mul_comm (a b : FixedPoint 42 24)
  : (f_mul a b) = (f_mul b a) := by
  simp [f_mul, Bool.xor_comm, BitVec.mul_comm]

theorem FP16_e_mul_comm (a b : EFixedPoint 42 24)
  : (e_mul a b) = (e_mul b a) := by
  simp [e_mul]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp_all [Bool.xor_comm, FP16_f_mul_comm]

theorem FP16_mulfixed_comm (a b : PackedFloat 5 10) (m : RoundingMode)
  : (mulfixed (by omega) a b m) = (mulfixed (by omega) b a m) := by
  simp [mulfixed, FP16_e_mul_comm]

-- Division

theorem FP16_div_one_is_id (a : PackedFloat 5 10) (h : ¬a.isNaN)
  : div a oneE5M10 .RTZ = a := by
  apply PackedFloat.inj
  simp at h
  simp [oneE5M10, div, div_numbers, round, BitVec.cons, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem FP16_div_self_is_one (a : PackedFloat 5 10)
  (h : ¬a.isNaN ∧ ¬a.isInfinite ∧ ¬a.isZero)
  : (div a a .RTZ) = oneE5M10 := by
  apply PackedFloat.inj
  simp at h
  simp [div, div_numbers, round, BitVec.cons, oneE5M10,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

-- Other

theorem FP16_sterbenzFP16 (a b : PackedFloat 5 10)
  (h : le a (doubleRNE b) ∧ le b (doubleRNE a))
  : isExactFloat 5 10 (e_add .RTZ (a.toEFixed (by omega)) ((neg b).toEFixed (by omega)))
  := by
  simp [le, doubleRNE] at h
  simp [e_add, f_add, neg, round, isExactFloat,
    PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
