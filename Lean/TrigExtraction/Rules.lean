import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Lean Elab Term Meta PrettyPrinter
open Real

structure RewriteRuleTerms where
  name : String
  lhs : term
  rhs : term

-- def trigRules : Array RewriteRuleTerms :=
--   [

--   ]
inductive Direction where
  | left_to_right
  | right_to_left
  | both

axiom pow_one_rule : ∀ (x : ℝ), x ^ 1 = x
axiom zpow_succ : ∀ (x : ℝ) (y : ℤ), x ^ (y + 1) = x ^ y * x

-- field axioms
def baseRules : List Name :=
  [
    -- semiring
    ``Lean.Grind.Semiring.add_zero,
    ``Lean.Grind.Semiring.add_comm,
    ``Lean.Grind.Semiring.add_assoc,
    ``Lean.Grind.Semiring.mul_assoc,
    ``Lean.Grind.Semiring.mul_one,
    ``Lean.Grind.Semiring.one_mul,
    ``Lean.Grind.Semiring.left_distrib,
    ``Lean.Grind.Semiring.right_distrib,
    ``Lean.Grind.Semiring.zero_mul,
    ``Lean.Grind.Semiring.mul_zero,
    ``Lean.Grind.Semiring.pow_zero,
    ``Lean.Grind.Semiring.pow_succ,
    -- commsemiring
    ``Lean.Grind.CommSemiring.mul_comm,
    -- -- ring
    ``Lean.Grind.Ring.neg_add_cancel,
    ``Lean.Grind.Ring.sub_eq_add_neg,
    ``Lean.Grind.Ring.neg_zsmul,
    -- field needs to define inv
    -- ``Lean.Grind.Field.inv_zero,
    -- ``Lean.Grind.Field.mul_inv_cancel, causes bugs
    ``Lean.Grind.Field.zpow_zero,
    ``Lean.Grind.Field.zpow_succ,
    ``Lean.Grind.Field.zpow_neg,
    ``pow_one_rule

  ]

def baseRulesDirectional :=
  [
    (``Lean.Grind.Semiring.add_zero, Direction.both),
    (``Lean.Grind.Semiring.add_comm, Direction.left_to_right), -- once is probably enough
    (``Lean.Grind.Semiring.add_assoc, Direction.both),
    (``Lean.Grind.Semiring.mul_assoc, Direction.both),
    (``Lean.Grind.Semiring.mul_one, Direction.left_to_right),
    (``Lean.Grind.Semiring.one_mul, Direction.left_to_right),
    (``Lean.Grind.Semiring.left_distrib, Direction.left_to_right),
    (``Lean.Grind.Semiring.zero_mul, Direction.left_to_right),
    (``Lean.Grind.Semiring.mul_zero, Direction.left_to_right),
    (``Lean.Grind.Semiring.pow_zero, Direction.left_to_right),
    (``Lean.Grind.Semiring.pow_succ, Direction.both),
    (``Lean.Grind.Ring.neg_add_cancel, Direction.both),
    (``Lean.Grind.Ring.sub_eq_add_neg, Direction.both),
    (``Lean.Grind.Field.zpow_zero, Direction.left_to_right),
    (``zpow_succ, Direction.both),
    (``Lean.Grind.Field.zpow_neg, Direction.both),
    (``pow_one_rule, Direction.both)
  ]

def trigRules : List Name :=
  [
    ``Real.cos_sq_add_sin_sq,
    ``Real.tan_eq_sin_div_cos,
    ``Real.sin_neg,
    ``Real.cos_neg,
    ``Real.sin_antiperiodic,
    ``Real.cos_antiperiodic,
    ``Real.tan_periodic,
    ``Real.sin_periodic,
    ``Real.cos_periodic,
    ``Real.sin_zero,
    ``Real.cos_zero,
    ``Real.tan_zero,
    ``Real.sin_pi_div_six,
    ``Real.cos_pi_div_six,
    ``Real.tan_pi_div_six,
    ``Real.sin_pi_div_four,
    ``Real.cos_pi_div_four,
    ``Real.tan_pi_div_four,
    ``Real.sin_pi_div_three,
    ``Real.cos_pi_div_three,
    ``Real.tan_pi_div_three,
    ``Real.sin_pi_div_two,
    ``Real.cos_pi_div_two,
    ``Real.sin_sq_eq_half_sub,
    ``Real.two_mul_sin_mul_cos,
    ``Real.two_mul_cos_mul_cos,
    ``Real.two_mul_sin_mul_sin,
    ``Real.sin_sub_sin,
    ``Real.cos_add_cos,
    ``Real.cos_sub_cos,
    ``Real.cos_add,
    ``Real.sin_add,
    ``Real.cos_sub,
    ``Real.sin_sub,
    ``Real.sin_two_mul,
    ``Real.cos_two_mul,
    ``Real.cos_two_mul',
  ] ++ baseRules

def trigRulesDirectional :=
  [
    (``Real.cos_sq_add_sin_sq, Direction.left_to_right),
    (``Real.tan_eq_sin_div_cos, Direction.both),
    (``Real.sin_neg, Direction.both),
    (``Real.cos_neg, Direction.both),
    (``Real.sin_antiperiodic, Direction.both),
    (``Real.cos_antiperiodic, Direction.both),
    (``Real.tan_periodic, Direction.both),
    (``Real.sin_periodic, Direction.both),
    (``Real.cos_periodic, Direction.both),
    (``Real.sin_zero, Direction.left_to_right),
    (``Real.cos_zero, Direction.left_to_right),
    (``Real.tan_zero, Direction.left_to_right),
    (``Real.sin_pi_div_six, Direction.left_to_right),
    (``Real.cos_pi_div_six, Direction.left_to_right),
    (``Real.tan_pi_div_six, Direction.left_to_right),
    (``Real.sin_pi_div_four, Direction.left_to_right),
    (``Real.cos_pi_div_four, Direction.left_to_right),
    (``Real.tan_pi_div_four, Direction.left_to_right),
    (``Real.sin_pi_div_three, Direction.left_to_right),
    (``Real.cos_pi_div_three, Direction.left_to_right),
    (``Real.tan_pi_div_three, Direction.left_to_right),
    (``Real.sin_pi_div_two, Direction.left_to_right),
    (``Real.cos_pi_div_two, Direction.left_to_right),
    (``Real.sin_sq_eq_half_sub, Direction.both),
    (``Real.two_mul_sin_mul_cos, Direction.both),
    (``Real.two_mul_cos_mul_cos, Direction.both),
    (``Real.two_mul_sin_mul_sin, Direction.both),
    (``Real.sin_sub_sin, Direction.both),
    (``Real.cos_add_cos, Direction.both),
    (``Real.cos_sub_cos, Direction.both),
    (``Real.cos_add, Direction.both),
    (``Real.sin_add, Direction.both),
    (``Real.cos_sub, Direction.both),
    (``Real.sin_sub, Direction.both),
    (``Real.sin_two_mul, Direction.both),
    (``Real.cos_two_mul, Direction.both),
    (``Real.cos_two_mul', Direction.both)
  ] ++ baseRulesDirectional

def testDirectionalRule : List (Name × Direction) :=
  [
    (``Lean.Grind.Semiring.add_zero, Direction.both)
  ]
