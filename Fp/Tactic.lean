import Lean
open Lean Meta Elab Tactic

register_simp_attr bv_float

-- way 1: write a macro.
macro_rules |
    `(tactic| decreasing_trivial) => `(tactic| simp [bv_float]; bv_decide)

theorem foo : 1 = 2 := by decreasing_trivial

#print foo


/--
info: inductive Lean.Expr : Type
number of parameters: 0
constructors:
Lean.Expr.bvar : Nat → Expr
Lean.Expr.fvar : FVarId → Expr
Lean.Expr.mvar : MVarId → Expr -- metavariables
Lean.Expr.sort : Level → Expr
Lean.Expr.const : Name → List Level → Expr
Lean.Expr.app : Expr → Expr → Expr
Lean.Expr.lam : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.forallE : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.letE : Name → Expr → Expr → Expr → Bool → Expr
Lean.Expr.lit : Literal → Expr
Lean.Expr.mdata : MData → Expr → Expr
Lean.Expr.proj : Name → Nat → Expr → Expr
-/
#guard_msgs in #print Lean.Expr
namespace MinimalBoilerplate

-- 1. add a new production rule into the lean grammar
-- "tactic" -[myCoolTacName]-> "my_cool_tactic"

syntax (name := myCoolTacName) "my_cool_tactic" : tactic


-- contains the values of *fvars* (i.e. free variables), which are internally just integers,
-- but are used to represent stuff that's to the left of the turnstile.
-- so, it maps 'FVarId's to lean 'Expr's, and everyone else indexes using 'FvarId's.
#check LocalContext

-- abbrev Tactic  := Syntax → TacticM Unit
@[tactic myCoolTacName]
def evalBvAutomataCircuit : Tactic := fun stx =>
  match stx with
  -- | in the non-terminal called tactic, I match on the identifier 'my_cool_tactic'
  | `(tactic| my_cool_tactic) => do -- special 'syntax matching' lean syntax
     -- ⊢ TacticM Unit
     -- the current tactic state is a list of *goals*, where each 'goal' is a
     --  [metavariable] / MVarId
     -- ⊢ goals : (List MVarId)
        -- h : 5 = 6
        -- ⊢ ?e : 3 = 4
        -- expression, of type '3 = 4', in a context with the hypotheis '5 = 6',
        --  with no value currently.
     -- let goals ← getGoals
     let mainGoal ← getMainGoal
     -- use the LocalContext of 'mainGoal'.
     mainGoal.withContext do
       -- ?e : 3 = 4
       -- ?e =isdefEq= (sorry : 3 = 4)
       --- > oh, ?e is a meta-variable that's un-assigned, so I'm
       --- gonna assign it 'sorry'.
       --- ?e := sorry
       let eValue ← mkSorry (← mainGoal.getType) (synthetic := true)
       -- mainGoal.assign sorry
       if ← isDefEq (Expr.mvar mainGoal) eValue then
         logInfo m!"hurray, closed goal {mainGoal}"
       else
         throwError "error: unable to assign 'sorry' to {mainGoal}"



     -- logInfo m!"whoa there buddy, you made an error: {goals}"
     -- setGoals []
  | _ =>
    -- exception to communicate that this particular pattern match does not
    -- know what's going on with the syntax that's been given to it.
    throwUnsupportedSyntax

example (x : BitVec w) : BitVec w :=
    x.zeroExtend _
    -- ?mvar : Nat
    -- ... ?mvar = w

theorem bar (h : 5 = 6) : 3 = 4 ∧ 5 = 6 := by
   -- ?g1 : 5 = 6 ⊢ 3 = 4 ∧ 5 = 6
   constructor
   -- ?g1 := 5 = 6 ⊢ And.intro ?g2  ?g3
   -- ?g2 : 5 = 6 ⊢ 3 = 4
   -- ?g3 : 5 = 6 ⊢ 5 = 6
   · my_cool_tactic
   · my_cool_tactic
   -- · sorry-- ?g2 := mkSorry
   -- · exact h -- ?g3 := h

-- fun h => ⟨sorry, h⟩
/--
info: theorem MinimalBoilerplate.bar : 5 = 6 → 3 = 4 ∧ 5 = 6 :=
fun h => ⟨sorry, sorry⟩
-/
#guard_msgs in #print bar

end MinimalBoilerplate



namespace FullBoilerplate
structure Config where
/-- Allow elaboration of `bv_automata_gen's config` arguments to tactics. -/
declare_config_elab elabBvAutomataCircuitConfig Config

syntax (name := bvAutomataGen) "my_cool_tactic" (Lean.Parser.Tactic.config)? : tactic
@[tactic bvAutomataGen]
def evalBvAutomataCircuit : Tactic := fun
| `(tactic| my_cool_tactic $[$cfg]?) => do
  let cfg ← elabBvAutomataCircuitConfig (mkOptionalNode cfg)
  let g ← getMainGoal
  g.withContext do
     throwError "whoa there buddy, you made an error"
| _ => throwUnsupportedSyntax
end FullBoilerplate
