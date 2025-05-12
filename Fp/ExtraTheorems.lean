import Fp.Basic
import Fp.Addition
import Fp.Multiplication
import Fp.Rounding

def twoE5M2 : PackedFloat 5 2 := PackedFloat.ofBits _ _ 0b01000000

theorem add_eq_mul_two (a : PackedFloat 5 2) (m : RoundingMode)
  : add (by omega) a a m = mul two a m := by
  apply PackedFloat.inj
  simp [add, e_add, f_add, twoE5M2, PackedFloat.toEFixed, mul, round,
        BitVec.cons, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  --bv_decide
  sorry
