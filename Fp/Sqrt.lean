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
  sqrt_iter x 0 (n/2)

@[bv_float_normalize]
def sqrt_impl (x : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  let sig' :=
    BitVec.ofBool (x.ex != 0) ++ x.sig
  let sig_shift : BitVec (s+2) :=
    sig'.setWidth _ <<< BitVec.ofBool (x.ex != 0 && (x.ex &&& 1#e) == 0)
  let sqrtOperand : BitVec (2*s+6) := sig_shift.setWidth _ <<< (s+4)
  let sqrtResult := bit_sqrt sqrtOperand
  let bias : Nat := 2^(e-1) - 1
  let exp' : BitVec e :=
    if x.ex = 0 then
      (bias + 1) / 2
    else if x.ex ≥ bias
    then (x.ex - bias) / 2 + bias
    else bias - (bias - x.ex + 1) / 2
  let result : EFixedPoint (2^e + s + 2) (bias + s + 2) :=
    {
      state := .Number
      num := {
        sign := false
        val := sqrtResult.setWidth _ <<< (exp' - 1)
        hExOffset := by
          have h := Nat.two_pow_pos e
          have h2 := two_pow_sub_one_le_two_pow e
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
