import Lean
import Fp.Tactics.Attributes
import Fp.Tactics.Simps

syntax (name := bvFloat) "bv_float_normalize" : tactic

macro_rules |
  `(tactic| bv_float_normalize) => `(tactic| simp only [bv_float_normalize] at *)
