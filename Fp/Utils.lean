-- Exponent bias typically follows the below standard forumula
def exBias_of_exWidth (exWidth : Nat) : Nat :=
  2 ^ (exWidth - 1) - 1

-- not used anywhere rn
theorem sub_two_lt { n : Nat } : n - 2 ≤ n := by
  omega
