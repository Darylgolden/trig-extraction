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
    -- ring
    ``Lean.Grind.Ring.neg_add_cancel,
    ``Lean.Grind.Ring.sub_eq_add_neg,
    -- field needs to define inv

  ]
def trigRules : List Name :=
  [
    ``Real.cos_sq_add_sin_sq,
  ] ++ baseRules
