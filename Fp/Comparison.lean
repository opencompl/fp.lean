import Fp.Basic
import Fp.Addition

@[simp]
def f_lt (a b : FixedPoint w e) : Bool :=
  (a.sign && b.sign && b.val < a.val) ∨
  (a.sign && ¬b.sign && (a.val ≠ 0 || b.val ≠ 0)) ∨
  (¬a.sign && ¬b.sign && a.val < b.val)

@[simp]
def e_lt (a b : EFixedPoint w e) : Bool :=
  a.state != .NaN && b.state != .NaN && (
    (a.state = .Infinity && a.num.sign && (b.state = .Number || ¬b.num.sign)) ||
    (b.state = .Infinity && ¬b.num.sign && (a.state = .Number || a.num.sign)) ||
    (a.state = .Number && b.state = .Number && f_lt a.num b.num)
  )

@[simp]
def e_le (a b : EFixedPoint w e) : Bool :=
  a.equal b || e_lt a b

@[simp]
def lt (a b : PackedFloat w e) : Bool :=
  let comp (x y : PackedFloat w e) :=
    x.ex < y.ex || (x.ex == y.ex && x.sig < y.sig)
  ¬a.isNaN && ¬b.isNaN && (
    (a.sign && b.sign && comp b a) ||
    (a.sign && ¬b.sign && (¬a.isZero || ¬b.isZero)) ||
    (¬a.sign && ¬b.sign && comp a b)
  )

@[simp]
def eq (a b : PackedFloat w e) : Bool :=
  ¬a.isNaN && ¬b.isNaN && (
    (a.sign == b.sign && a.ex == b.ex && a.sig == b.sig) ||
    (a.ex == 0 && b.ex == 0 && a.sig == 0 && b.sig == 0)
  )

@[simp]
def le (a b : PackedFloat w e) : Bool :=
  eq a b || lt a b

theorem e_lt_nan (a : EFixedPoint w e)
  : ¬(e_lt a (EFixedPoint.getNaN a.num.hExOffset)) := by
  simp [e_lt]

theorem nan_lt_e (a : EFixedPoint w e)
  : ¬(e_lt (EFixedPoint.getNaN a.num.hExOffset) a) := by
  simp [e_lt]

theorem e_lt_of_lt (a b : PackedFloat 5 2)
  : lt a b ↔ e_lt (a.toEFixed (by omega)) (b.toEFixed (by omega)) := by
  simp [PackedFloat.toEFixed]
  bv_decide

theorem le_of_e_le (m : RoundingMode) (a b : EFixedPoint 35 16)
  : e_le a b → le (round 5 2 m a) (round 5 2 m b) := by
  simp [round, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

theorem e_le_of_le (a b : PackedFloat 5 2)
  : le a b → e_le (a.toEFixed (by omega)) (b.toEFixed (by omega)) := by
  simp [PackedFloat.toEFixed]
  bv_decide
