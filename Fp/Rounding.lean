import Fp.Basic

inductive RoundingMode : Type
| RNE : RoundingMode -- RoundNearestTiesToEven
| RNA : RoundingMode -- RoundNearestTiesToAway
| RTP : RoundingMode -- RoundTowardPositive
| RTN : RoundingMode -- RoundTowardNegative
| RTZ : RoundingMode -- RoundTowardZero

/--
Find the position of the last (most significant) set bit in a BitVec.

Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.
-/
def fls (b : BitVec n) : BitVec n :=
  if n = 0 then 0
  else if BitVec.msb b then n
  else BitVec.truncate _ (fls (BitVec.truncate (n-1) b))
  termination_by n

-- Test threorems to see if bv_decide works
theorem fls_b (b : BitVec 7) :
  fls (fls b) <= 3 := by
  simp [fls]
  bv_decide

theorem toEFixed_test (f : PackedFloat 5 2)
  : (PackedFloat.toEFixed f (by omega)).num.val ≠ 60 := by
  simp [PackedFloat.toEFixed]
  simp only [← BitVec.shiftLeft_eq']
  bv_decide

-- TODO: Implement different rounding modes
def round (exWidth sigWidth : Nat)
  : EFixedPoint width exOffset -> PackedFloat exWidth sigWidth :=
  sorry
