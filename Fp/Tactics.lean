import Lean

register_simp_attr bv_float_normalize

syntax (name := bvFloat) "bv_float_normalize" : tactic

macro_rules |
  `(tactic| bv_float_normalize) => `(tactic| simp [bv_float_normalize,
    -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq'] at *)
