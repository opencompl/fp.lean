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
  else BitVec.setWidth' (by omega) (fls (BitVec.truncate (n-1) b))
  termination_by n

#eval fls 0x10#9

/--
Gets the first w bits of the bitvector v.
-/
def truncateRight (w : Nat) (v : BitVec n) : BitVec w :=
  if hw : n ≤ w then
    -- Have to show that hw ⊢ n + (w - n) = w
    BitVec.setWidth' (by omega) (v ++ 0#(w-n))
  else
    BitVec.truncate w (v >>> (n-w))

#eval truncateRight 4 0xaf#8
#eval truncateRight 16 0xaf#8

-- TODO: Implement different rounding modes
def round (exWidth sigWidth : Nat) (x : EFixedPoint width exOffset)
  : PackedFloat exWidth sigWidth :=
  if x.state == .NaN then
    PackedFloat.getNaN _ _
  else if x.state == .Infinity then
    PackedFloat.getInfinity _ _ x.num.sign
  else
    let exOffsetB : BitVec width := BitVec.ofNat _ exOffset
    let exOffset' := 2^(exWidth - 1) + sigWidth - 2
    -- trim bitvector
    let over := x.num.val >>> (exOffset + 2^(exWidth-1))
    let a := BitVec.truncate (2^(exWidth-1)) (x.num.val >>> exOffsetB)
    let b := truncateRight exOffset' (BitVec.truncate exOffset x.num.val)
    let _under := BitVec.truncate (exOffset - exOffset') x.num.val
    let trimmed := a ++ b
    if over != 0 then
      -- Overflow to Infinity
      PackedFloat.getInfinity _ _ x.num.sign
    else
    let index := fls trimmed
    let sigWidthB := BitVec.ofNat _ sigWidth
    if index ≤ sigWidthB then
      -- denormal
      {
        sign := x.num.sign
        ex := 0
        sig := BitVec.truncate _ trimmed
      }
    else
      let ex := BitVec.truncate _ (index - sigWidthB)
      let ex' := ex - 1#_
      -- Normal
      {
        sign := x.num.sign
        ex
        sig := BitVec.truncate _ (trimmed >>> (ex'))
      }

-- Test threorems to see if bv_decide works
theorem fls_b (b : BitVec 7) :
  fls (fls b) <= 3 := by
  simp [fls]
  bv_decide

-- Can go up to 4, 1 without overflow erroring
theorem round_leftinv_toEFixed (x : PackedFloat 2 1) (hx : ¬ x.isNaN):
  (round _ _ (PackedFloat.toEFixed x (by omega))) = x := by
  apply PackedFloat.inj
  simp at hx
  simp [round, fls, truncateRight, PackedFloat.toEFixed, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem round_b (b : FixedPoint 3 1) :
  (round 5 2 { state := .Number, num := b }).ex ≠ BitVec.allOnes _ := by
  simp [round, fls, truncateRight]
  -- bv_decide fails here
  sorry

theorem toEFixed_test (f : PackedFloat 5 2)
  : (PackedFloat.toEFixed f (by omega)).num.val ≠ 60 := by
  simp [PackedFloat.toEFixed, -BitVec.shiftLeft_eq']
  bv_decide

theorem getSignificand_append_truncate_test (v : BitVec 5)
  : (BitVec.truncate 3 v.reverse).reverse = truncateRight 3 v := by
  simp [truncateRight, BitVec.reverse, BitVec.concat]
  bv_decide
