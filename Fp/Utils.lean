import Std.Tactic.BVDecide

-- Exponent bias typically follows the below standard forumula
def exBias_of_exWidth (exWidth : Nat) : Nat :=
  2 ^ (exWidth - 1) - 1

-- not used anywhere rn
theorem sub_two_lt { n : Nat } : n - 2 ≤ n := by
  omega

theorem le_two_pow : n ≤ 2^n := by
  induction n
  case zero =>
    exact Nat.zero_le _
  case succ ih =>
    simp only [Nat.pow_add_one, Nat.mul_two]
    exact Nat.add_le_add ih Nat.one_le_two_pow
