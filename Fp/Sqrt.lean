import Fp.Basic
import Fp.Rounding

/-- Implementation of integer square root. -/
@[bv_float_normalize]
def sqrt_iter (x : BitVec n) (w : BitVec n) (i : Nat) : BitVec (n+1) :=
  let w' := w.setWidth (2*n) ||| (1#_ <<< i)
  let flag := (BitVec.ofBool (w' * w' ≤ x.setWidth (2*n))).setWidth n <<< i
  let w'' := w ||| flag
  if i = 0 then
      w'' ++ BitVec.ofBool (w''.setWidth (2*n) * w''.setWidth (2*n) ≠ x.setWidth (2*n))
  else
    sqrt_iter x w'' (i-1)

@[bv_float_normalize]
def bit_sqrt (x : BitVec n) : BitVec (n+1) :=
  sqrt_iter x 0 ((n-1)/2)

@[bv_float_normalize]
def sqrt_impl (x : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  let sig' :=
    BitVec.ofBool (x.ex != 0) ++ x.sig
  let sig_shift : BitVec (s+2) :=
    sig'.setWidth _ <<< BitVec.ofBool (x.ex != 0 && (x.ex &&& 1#e) == 0)
  -- We require a shift that
  -- * Is at least 2s to ensure enough precision bits
  -- * moves the units digit to an even position so the square root is correct
  let align_shift := if s % 2 = 0 then 2*s else 2*s + 1
  let sqrtOperand : BitVec (3*s+4) := sig_shift.setWidth _ <<< align_shift
  let sqrtResult := bit_sqrt sqrtOperand
  let bias : Nat := 2^(e-1) - 1
  -- Determine exponent
  let exp' : BitVec e :=
    if x.ex = 0 then
      bias - bias / 2
    else if x.ex ≥ bias
    then (x.ex - bias) / 2 + bias
    else bias - (bias - x.ex + 1) / 2
  let result : EFixedPoint (2^(e-1) + 3*s + 4) (bias + (s + align_shift) / 2) :=
    {
      state := .Number
      num := {
        sign := false
        val := sqrtResult.setWidth _ <<< (exp' - 1)
        hExOffset := by
          have h := Nat.two_pow_pos (e-1)
          have h2 : align_shift ≤ 2*s+2 := by
            by_cases (s % 2 = 0) <;> simp_all [align_shift]
          omega
      }
    }
  round e s m result

@[bv_float_normalize]
def sqrt (x : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  if x.isZero then x
  else if x.sign || x.isNaN then PackedFloat.getNaN e s
  else if x.isInfinite then PackedFloat.getInfinity e s false
  else sqrt_impl x m

theorem square_sqrt_is_id (x : BitVec 5)
  : bit_sqrt (x.setWidth 10 * x.setWidth _) = x.setWidth _ <<< 1 := by
  bv_float_normalize
  bv_decide

/-- info: { sign := +, ex := 0x07#5, sig := 0x0#2 } -/
#guard_msgs in #eval sqrt (PackedFloat.ofBits 5 2 0b00000001#8) .RNE
/-- info: { sign := +, ex := 0x0f#5, sig := 0x0#2 } -/
#guard_msgs in #eval sqrt (oneE5M2) .RNE
