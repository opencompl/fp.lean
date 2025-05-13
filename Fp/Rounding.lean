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

-- TODO: Implement different rounding modes
-- Less well-behaved when exWidth = 0. This shouldn't be an issue?
def round
  (exWidth sigWidth : Nat) (mode : RoundingMode) (x : EFixedPoint width exOffset)
  : PackedFloat exWidth sigWidth :=
  if x.state = .NaN then
    PackedFloat.getNaN _ _
  else if x.state = .Infinity then
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
      -- Unless we're rounding RTN/RTP to the opposite sign, or RTZ
      -- in which case we overflow to MAX
      if (mode = .RTN ∧ ¬x.num.sign) ∨ (mode = .RTP ∧ x.num.sign) ∨ mode = .RTZ then
        PackedFloat.getMax _ _ x.num.sign
      else
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

def isExactFloat (exWidth sigWidth : Nat)
  (x : EFixedPoint width exOffset) : Bool :=
  if x.state = .Number then
    let exOffset' := 2^(exWidth - 1) + sigWidth - 2
    -- trim bitvector
    let over := x.num.val >>> (exOffset + 2^(exWidth-1))
    let a := (x.num.val >>> exOffset).truncate (2^(exWidth-1))
    let b := truncateRight exOffset' (x.num.val.truncate exOffset)
    let underWidth := exOffset - exOffset'
    let under := x.num.val.truncate underWidth
    let trimmed := a ++ b
    if over != 0 || under != 0 then
      -- Overflow to Infinity, or under has values
      false
    else
    let index := fls trimmed
    let sigWidthB := BitVec.ofNat _ sigWidth
    let ex : BitVec exWidth :=
      if index ≤ sigWidthB then
        0
      else
        (index - sigWidthB).truncate _
    if ex = 0 then
      true
    else
      let totalShift : BitVec (exWidth+1) := ex.truncate _ - 1
      (trimmed &&& ((1#_ <<< totalShift) - 1#_)) == 0
  else
    true

/--
Every floating point number converted to fixed point form, shall be an exact
floating point number.
-/
theorem toEFixed_isExactFloat (a : PackedFloat 5 2)
  : isExactFloat 5 2 (a.toEFixed (by omega)) := by
  simp [isExactFloat, PackedFloat.toEFixed,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

/--
If a fixed point number is an exact floating point number, then converting to
floating point and back should not change the denotation.
-/
theorem isExactFloat_round_toEFixed (a : EFixedPoint 34 16) (m : RoundingMode)
  (ha : isExactFloat 5 2 a)
  : a.equal_denotation ((round 5 2 m a).toEFixed (by omega)) := by
  simp [isExactFloat, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq'] at ha
  simp [PackedFloat.toEFixed, round,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

/-- info: 0x05#8 -/
#guard_msgs in #eval fls 0x10#8
/-- info: 0x00#8 -/
#guard_msgs in #eval fls 0#8
/-- info: 0xa#4 -/
#guard_msgs in #eval truncateRight 4 0xaf#8
/-- info: 0xaf00#16 -/
#guard_msgs in #eval truncateRight 16 0xaf#8
