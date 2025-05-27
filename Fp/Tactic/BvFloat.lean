import Lean
import Fp.Tactic.Attr
import Fp.Addition


syntax (name := bvFloat) "bv_float_normalize" : tactic

-- run bv_float_normalize everywhere, followd by 'bv_decide'.
macro_rules |
  `(tactic| bv_float_normalize) => `(tactic| simp only [bv_float_normalize] at *)



-- way 1 to add rules to bv_float_normalize: tag theorem definitions with bv_float_normalize
--  @[simp bv_float_normalize]
-- way 2 to add rules: write 'simproc's.
    -- + somewhere in between the expressiveness of just tagging a defn, versus writing a full tactic yourself.
    -- + hook into simp's rewriting engine, by adding a custom rewrite logic rule.

attribute [bv_float_normalize] add
attribute [bv_float_normalize] round
attribute [bv_float_normalize] e_add
attribute [bv_float_normalize] f_add
attribute [bv_float_normalize] PackedFloat.toEFixed
attribute [bv_float_normalize] PackedFloat.isNaN
attribute [bv_float_normalize] PackedFloat.isInfinite
attribute [bv_float_normalize] EFixedPoint.getInfinity
attribute [bv_float_normalize] EFixedPoint.getNaN

/-
@[bv_float_normalize]
theorem injEq' (a b : PackedFloat e s)
  :  (a = b) = (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) := by sorry
-/

/-
@[ext]
theorem injEq' (a b : PackedFloat e s) (h : ((a.sign, a.ex, a.sig) = (b.sign, b.ex, b.sig)))
  :  (a = b)  := sorry
-/

-- sadly, fails, because Lean expects hyp to be '_ = _'
/-
@[ext]
theorem injEq' (a b : PackedFloat e s) (h : (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig))
  :  (a = b)  := sorry
-/



/--
info: structure Lean.Meta.Simp.Result : Type
number of parameters: 0
fields:
  Lean.Meta.Simp.Result.expr : Lean.Expr
  Lean.Meta.Simp.Result.proof? : Option Lean.Expr :=
    none
  Lean.Meta.Simp.Result.cache : Bool :=
    true
constructor:
  Lean.Meta.Simp.Result.mk (expr : Lean.Expr) (proof? : Option Lean.Expr) (cache : Bool) : Lean.Meta.Simp.Result
-/
#guard_msgs in #print Lean.Meta.Simp.Result

-- info: inductive Lean.Meta.Simp.Step : Type
-- number of parameters: 0
-- constructors:
-- Lean.Meta.Simp.Step.done : Lean.Meta.Simp.Result → Lean.Meta.Simp.Step
-- Lean.Meta.Simp.Step.visit : Lean.Meta.Simp.Result → Lean.Meta.Simp.Step
-- Lean.Meta.Simp.Step.continue : optParam (Option Lean.Meta.Simp.Result) none → Lean.Meta.Simp.Step
/-
#guard_msgs in #print Lean.Meta.Simp.Step
simproc injEq_simproc (@Eq (PackedFloat _ _) _  _) := fun e =>
  -- e : Lean.Expr
  -- ⊢ Lean.Meta.SimpM Lean.Meta.Simp.Step
  -- "hurray, simproc matched"
  return .done ({ .expr := e }
-/

-- attribute [bv_float_normalize] injEq_simproc




theorem foo (x y : PackedFloat 3 4) : add x y .RNE = add y x .RNE := by
  bv_float_normalize
  simp [-BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide

  -- apply PackedFloat.inj


  -- bv_float_normalize
  -- -- TODO for tunan: move the requisite ones into bv_float_normalize, except for the ones
  -- -- that are already covered by bv_normalize

  -- simp only [Nat.reducePow, Nat.reduceAdd, Nat.add_one_sub_one, Nat.reduceSub, BitVec.reduceAllOnes,
  --   BitVec.ofNat_eq_ofNat, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_false,
  --   PackedFloat.isZeroOrSubnorm, BitVec.setWidth'_eq, Bool.or_eq_true, decide_eq_true_eq,
  --   BitVec.add_eq, BitVec.sub_eq, reduceCtorEq, BitVec.zero_eq, dite_eq_ite, PackedFloat.getNaN,
  --   PackedFloat.getInfinity, Bool.not_eq_true, false_and, or_self, ↓reduceIte, shouldRoundAway,
  --   Nat.add_zero, fls, BitVec.truncate_eq_setWidth, truncateRight, Nat.le_refl, ↓reduceDIte,
  --   BitVec.append_zero_width, eq_mp_eq_cast, cast_eq, lastPowerOfTwo, Nat.reduceDiv,
  --   lastPowerOfTwo_iter.eq_1, Nat.add_one_ne_zero, Nat.reduceLT, fls_log.eq_1, Nat.zero_lt_succ,
  --   Nat.div_self, Nat.succ_ne_self, BitVec.or_zero, BitVec.reduceShiftRightShiftRight,
  --   ite_eq_left_iff, BitVec.not_le, Nat.reduceShiftLeft, BitVec.shiftLeft_eq_zero, Nat.sub_self,
  --   Nat.reduceLeDiff, BitVec.natCast_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
  --   BitVec.getLsbD_eq_getElem, Bool.decide_and, Bool.decide_eq_true, Bool.decide_or, decide_not,
  --   Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ite_not]
  -- bv_decide
