import Std.Tactic.BVDecide

@[simp]
def lastPowerOfTwo_iter (m : Nat) (n : Nat) : Nat :=
  if m = 0 then
    1
  else if 2 ^ m < n then
    2 ^ m
  else
    lastPowerOfTwo_iter (m-1) n
  termination_by m

/--
Returns the largest power of two strictly less than `n`.

If no such number exists, returns `1` instead.
-/
@[simp]
def lastPowerOfTwo (n : Nat) : Nat :=
  lastPowerOfTwo_iter ((n+1)/2) n

theorem sub_two_le { n : Nat } : n - 2 ≤ n := by
  omega

theorem le_two_pow : n ≤ 2^n := by
  induction n
  case zero =>
    exact Nat.zero_le _
  case succ ih =>
    simp only [Nat.pow_add_one, Nat.mul_two]
    exact Nat.add_le_add ih Nat.one_le_two_pow

theorem toEFixed_hExOffset : 2 ^ (e - 1) + s - 2 < 2 ^ e + s := by
  have h1 : 2 ^ (e - 1) + s - 2 ≤ 2^e + s - 2 := by
    refine Nat.sub_le_sub_right ?_ 2
    refine Nat.add_le_add_right ?_ s
    refine Nat.pow_le_pow_right ?_ ?_ <;> omega
  have h2 : 2^e + s - 2 ≤ 2^e + s - 1 := by omega
  apply Nat.lt_of_le_of_lt h1
  apply Nat.lt_of_le_of_lt h2
  apply Nat.sub_one_lt
  apply Nat.ne_zero_of_lt
  refine Nat.lt_add_of_pos_left ?_
  exact Nat.two_pow_pos e
