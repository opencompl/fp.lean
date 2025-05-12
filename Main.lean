import Fp

-- Idk how to prove in general
theorem ofBits_inv_toBits (x : PackedFloat 5 2)
  : PackedFloat.ofBits _ _ (x.toBits) = x := by
  simp
  bv_decide

structure OpResult where
  oper : String
  mode : RoundingMode
  result : List String

structure FP8Format where
  e : Nat
  m : Nat
  h8 : 1 + e + m = 8
  he : 0 < e

namespace FP8Format
theorem h (f : FP8Format)
  : BitVec (1 + f.e + f.m) = BitVec 8 := by simp only [f.h8]
end FP8Format

def toDigits (b : BitVec n) : String :=
  let b' := b.reverse
  String.join ((List.finRange n).map (fun i => b'[i].toNat.digitChar.toString))

instance : Repr OpResult where
  reprPrec res _ :=
    let joinedResults := String.intercalate "," (res.result)
    f!"{res.oper},{repr res.mode},{joinedResults}"

def allRoundingModes : List RoundingMode :=
  [.RNA, .RNE, .RTN, .RTP, .RTZ]

def test_add (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "add"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.toBits (add f.he a' b' m))].map toDigits
  }

def test_div (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "div"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.toBits (div a' b' m))].map toDigits
  }

def test_mul (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "mul"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.toBits (mul f.he a' b' m))].map toDigits
  }

def test_lt (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "lt"
    mode := m
    result := [a, b].map toDigits ++ [(lt a' b').toNat.digitChar.toString]
  }

def test_binop (f : RoundingMode → BitVec 8 → BitVec 8 → OpResult) : List OpResult :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).map (fun b =>
        f m (BitVec.ofNat 8 a) (BitVec.ofNat 8 b)
      )
    )
  )

def test_all (f : FP8Format) : List OpResult :=
  List.flatten [
    test_binop $ test_add f,
    test_binop $ test_lt f,
    test_binop $ test_mul f,
    test_binop $ test_div f
  ]

def e5m2 : FP8Format where
  e := 5
  m := 2
  h8 := by omega
  he := by omega

def e3m4 : FP8Format where
  e := 3
  m := 4
  h8 := by omega
  he := by omega

def main (args : List String) : IO Unit := do
  if args = ["e5m2"] then
    for res in test_all e5m2 do
      IO.println (repr res)
  else if args = ["e3m4"] then
    for res in test_all e3m4 do
      IO.println (repr res)
  else
      IO.println "Please run with command line arg e5m2 or e3m4"


/-- info: { sign := -, ex := 0x04#5, sig := 0x1#2 } -/
#guard_msgs in #eval add (by omega) (PackedFloat.ofBits 5 2 0b00000011#8) (PackedFloat.ofBits 5 2 0b10010001#8) .RNE
/-- info: { sign := +, ex := 0x01#5, sig := 0x2#2 } -/
#guard_msgs in #eval round 5 2 .RNE (PackedFloat.toEFixed {sign := false, ex := 1#5, sig := 2#2} (by omega))
/-- info: { sign := +, ex := 0x1f#5, sig := 0x2#2 } -/
#guard_msgs in #eval mul (by omega) (PackedFloat.getZero 5 2) (PackedFloat.getInfinity 5 2 true) .RTZ
/-- info: { sign := +, ex := 0x1f#5, sig := 0x0#2 } -/
#guard_msgs in #eval div (Tests.oneE5M2) (PackedFloat.getZero 5 2) .RTZ
/-- info: { sign := +, ex := 0x00#5, sig := 0x1#2 } -/
#guard_msgs in #eval mul (by omega) (PackedFloat.ofBits 5 2 0b00000001#8) (PackedFloat.ofBits 5 2 0b00111001#8) .RNE
