import Fp.Basic
import Fp.Rounding
import Fp.Addition
import Fp.Multiplication
import Fp.Comparison
import Fp.Division

-- Idk how to prove in general
theorem ofBits_inv_toBits (x : PackedFloat 5 2)
  : PackedFloat.ofBits _ _ (x.toBits) = x := by
  simp
  bv_decide

structure OpResult where
  oper : String
  mode : RoundingMode
  result : List String

def toDigits (b : BitVec n) : String :=
  let b' := b.reverse
  String.join ((List.finRange n).map (fun i => b'[i].toNat.digitChar.toString))

instance : Repr OpResult where
  reprPrec res _ :=
    let joinedResults := String.intercalate "," (res.result)
    f!"{res.oper},{repr res.mode},{joinedResults}"

def allRoundingModes : List RoundingMode :=
  [.RNE, .RNA, .RTP, .RTN, .RTZ]

def test_add (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits 5 2 a
  let b' := PackedFloat.ofBits 5 2 b
  {
    oper := "add"
    mode := m
    result := [a, b, PackedFloat.toBits (add (by omega) a' b' m)].map toDigits
  }

def test_div (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits 5 2 a
  let b' := PackedFloat.ofBits 5 2 b
  {
    oper := "div"
    mode := m
    result := [a, b, PackedFloat.toBits (div a' b' m)].map toDigits
  }

def test_mul (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits 5 2 a
  let b' := PackedFloat.ofBits 5 2 b
  {
    oper := "mul"
    mode := m
    result := [a, b, PackedFloat.toBits (mul (by omega) a' b' m)].map toDigits
  }

def test_lt (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits 5 2 a
  let b' := PackedFloat.ofBits 5 2 b
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

def test_all : Unit → List OpResult := fun () =>
  List.flatten [
    test_binop test_add,
    test_binop test_lt,
    test_binop test_mul,
    test_binop test_div
  ]

def main : IO Unit := do
  for res in test_all () do
    IO.println (repr res)
