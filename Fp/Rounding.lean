import Fp.Basic

inductive RoundingMode : Type
| RNE : RoundingMode -- RoundNearestTiesToEven
| RNA : RoundingMode -- RoundNearestTiesToAway
| RTP : RoundingMode -- RoundTowardPositive
| RTN : RoundingMode -- RoundTowardNegative
| RTZ : RoundingMode -- RoundTowardZero
deriving DecidableEq

instance : Repr RoundingMode where
  reprPrec m _ := match m with
  | .RNA => "RNA"
  | .RNE => "RNE"
  | .RTN => "RTN"
  | .RTP => "RTP"
  | .RTZ => "RTZ"

@[simp]
def fls' (m : Nat) (b : BitVec n) (hm : n ≤ m) : BitVec m :=
  if n = 0 then 0
  else if b.msb then n
  else fls' m (BitVec.truncate (n-1) b) (by omega)
  termination_by n

/--
Find the position of the last (most significant) set bit in a BitVec.

Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.
-/
@[simp]
def fls (b : BitVec n) : BitVec n :=
  fls' n b (n.le_refl)

#eval fls 0x10#8

/--
Gets the first w bits of the bitvector v.
-/
@[simp]
def truncateRight (w : Nat) (v : BitVec n) : BitVec w :=
  if hw : n ≤ w then
    -- Have to show that hw ⊢ n + (w - n) = w
    have h : BitVec (n+(w-n)) = BitVec w := by
      congr
      omega

    h.mp (v ++ 0#(w-n))
  else
    BitVec.truncate w (v >>> (n-w))

@[simp]
def shouldRoundAway (m : RoundingMode)
  (sign : Bool) (odd : Bool) (v : BitVec n) : Bool :=
  let guard := v.msb
  let sticky := v.truncate (n-1) ≠ 0
  match m with
  | .RNE => guard ∧ (sticky ∨ odd)
  | .RNA => guard
  | .RTP => (guard ∨ sticky) ∧ ¬sign
  | .RTN => (guard ∨ sticky) ∧ sign
  | .RTZ => False

#eval truncateRight 4 0xaf#8
#eval truncateRight 16 0xaf#8

-- TODO: Implement different rounding modes
-- Less well-behaved when exWidth = 0. This shouldn't be an issue?
def round
  (exWidth sigWidth : Nat) (mode : RoundingMode) (x : EFixedPoint width exOffset)
  : PackedFloat exWidth sigWidth :=
  if x.state == .NaN then
    PackedFloat.getNaN _ _
  else if x.state == .Infinity then
    PackedFloat.getInfinity _ _ x.num.sign
  else
    let exOffset' := 2^(exWidth - 1) + sigWidth - 2
    -- trim bitvector
    let over := x.num.val >>> (exOffset + 2^(exWidth-1))
    let a := (x.num.val >>> exOffset).truncate (2^(exWidth-1))
    let b := truncateRight exOffset' (x.num.val.truncate exOffset)
    let underWidth := exOffset - exOffset'
    let under := x.num.val.truncate underWidth
    let trimmed := a ++ b
    if over != 0 then
      -- Overflow to Infinity
      PackedFloat.getInfinity _ _ x.num.sign
    else
    let index := fls trimmed
    let sigWidthB := BitVec.ofNat _ sigWidth
    let ex : BitVec exWidth :=
      if index ≤ sigWidthB then
        0
      else
        (index - sigWidthB).truncate _
    let truncSig : BitVec sigWidth :=
      if ex = 0 then
        trimmed.truncate _
      else
        (trimmed >>> (ex - 1)).truncate _
    let rem : BitVec (2^exWidth + underWidth) :=
      if ex = 0 then
        under.truncate _ <<< (1<<<exWidth)
      else
        let totalShift : BitVec (exWidth+1) := ex.truncate _ - 1
        truncateRight _ (trimmed <<< ((1<<<exWidth) + sigWidth - 2 - totalShift)) |||
        (under.truncate _ <<< ((1<<<exWidth) - totalShift))
    if shouldRoundAway mode x.num.sign (truncSig.getLsbD 0) rem then
      if truncSig = BitVec.allOnes _ then
        -- overflow to next exponent
        {
          sign := x.num.sign
          ex := ex+1
          sig := 0
        }
      else
        {
          sign := x.num.sign
          ex
          sig := truncSig + 1
        }
    else
    {
      sign := x.num.sign
      ex
      sig := truncSig
    }

-- Theorem: Fixed -> Float is left inverse to Float -> Fixed
-- Can go up to 4, 1 without overflow erroring
theorem round_leftinv_toEFixed (x : PackedFloat 5 2) (mode : RoundingMode) (hx : ¬ x.isNaN):
  (round _ _ mode (x.toEFixed (by omega))) = x := by
  apply PackedFloat.inj
  simp at hx
  simp [round, PackedFloat.toEFixed, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

-- Test threorems to see if bv_decide works
theorem fls_b (b : BitVec 7) :
  fls (fls b) <= 5 := by
  simp
  bv_decide

theorem round_b (b : FixedPoint 3 1) (mode : RoundingMode) :
  (round 5 1 mode { state := .Number, num := b }).ex ≠ BitVec.allOnes _ := by
  simp [round]
  bv_decide

theorem toEFixed_test (f : PackedFloat 5 2)
  : (f.toEFixed (by omega)).num.val ≠ 60 := by
  simp [PackedFloat.toEFixed, -BitVec.shiftLeft_eq']
  bv_decide

theorem getSignificand_append_truncate_test (v : BitVec 5)
  : (BitVec.truncate 3 v.reverse).reverse = truncateRight 3 v := by
  simp [BitVec.reverse, BitVec.concat]
  bv_decide
