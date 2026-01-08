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
axiom pow_one_rule : ∀ (x : ℝ), x ^ 1 = x

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
