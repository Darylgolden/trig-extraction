import TrigExtraction.Basic
import TrigExtraction.Egg
import TrigExtraction.Language
import TrigExtraction.Commands
import Lean.Elab.Term
import Lean.PrettyPrinter
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Lean Elab Term Meta PrettyPrinter
open Real




variable (x y : ℝ)


-- #check showRawElab 2 * sin x
-- #check exprSyntaxToAST ((1 + 2) * 3)
-- #check exprSyntaxToAST (1 + 2 * 3)
-- #check exprSyntaxToAST (1 * 2 + 3)
-- #check exprSyntaxToAST (sin x + sin x)
-- #check exprSyntaxToAST (sin x)
-- #check exprSyntaxToAST (2.5 * sin x)
-- #check toEggStringExpr (2.5 * sin x)
-- #check toEggStringExpr ((1 + 2) * 3)
-- #check toEggStringExpr (sin x + sin x)
-- #check toEggStringExpr (2^2)
-- #check toEggStringRule ((sin x)^2 + (cos y)^2)

-- #check getASTSize (2.0 * sin x)
-- -- 4
-- #check getASTSize ((1 + 2) * 3)

#check Real.tan_mul_cos

#check sin_add
#print_lhs_rhs_metavars sin_add

-- #parse_equalities Real.sin_add
-- #runEggTest ((cos x)^2 + (sin x)^2)
-- #runEggTest x + 0
-- #runEggTestDirectional x + 0

-- -- #runEggTest x + 1
-- -- #runEggTest (1 - (sin x)^2)
-- -- #runEggTest sin ((1 + x) - x)^2 + (cos (1))^2
-- -- #runEggTest (1 + x) - x
-- -- #runEggTest (sin x) * (sin x) * (sin x) * (sin x)
-- #runEggTestDirectional tan ( tan x - sin x / cos x )
-- #runEggTestDirectional (1 + x) - x
-- #runEggTestDirectional sin (x  + y) + sin (x - y)
-- #runEggTestDirectional cos 1 * cos 3 + sin 1 * sin 3
-- #runEggTestDirectional cos 1 * cos 3 + sin 1 * sin 5
-- #runEggTestDirectional cos Real.pi
-- #runEggTestDirectional sin (1 + 2)
-- #runEggTestDirectional 30 + 60

-- #runEggTestDirectional sin (1 - 2)
-- #runEggTestDirectional cos (x + y) + cos (x - y)
-- #eval (30 + 60 : ℝ)
-- #runEggTestDirectional sin (x) ^ 2 + cos (x) ^ 2
-- #runEggTestDirectional 2 * ( sin x ) ^ 2 + 2 * ( cos x ) ^ 2
-- #runEggTestDirectional 2 * 1 + -2 * ( cos x ) ^ 2

-- #runEggTestDirectional -2 * ( cos x ) ^ 2 - 2 * -( cos x ) ^ 2


-- #runEggTestDirectional 1 - (1 /4) * ( sin (2 * x) ) ^ 2 - 1 * ( sin y ) ^ 2 - 1 * ( cos x )^4
-- #runEggTestDirectional (0.5 + 0.5)
-- need to debug decimals
-- #reduce (0 : ℝ)^0
-- #runEggTestDirectional cos 1 * cos 3 + sin 1 * sin 11
-- #runEggTestDirectional cos 1 * cos 3 + sin 1 * sin 0

-- -- -- #runEggTest Real.pi
-- -- #printASTSize Real.pi
-- -- #printASTSize 1
-- example : 1 + 1 = 2 := by norm_num
-- #check TermElabM
-- #reduce (0.5 : ℝ)^0
-- #norm_num (0 : ℝ) ^ ( -1 : ℤ)
-- example : (0 : ℝ) ^ ( -1 : ℤ) = 0 := by norm_num
-- #eval 0/0
-- #eval syntaxToAST 0.5 + 0.5
-- #eval syntaxToAST (1/2) + (1/2)
-- #eval syntaxToAST 0.23
-- #runEggTestDirectional sin ( x ) ^ 2 * cos ( -x + x ) ^ 2
-- #sympyToAST sin(x)**2*cos(-x + x)**2
-- #sympyToAST sin(x)**(2*sin(x)**2 + cos(2*x) + 1)
-- #runEggOnSympyExpr 2*sin(x)**2 + cos(x)**2 - 1
-- #runEggOnSympyExpr 1 - cos(x)**2
-- #runEggOnSympyExpr 1 - cos(x)**2
-- #runEggOnSympyExpr 1 - cos(x)**2

-- #runEggTestDirectional Real.sqrt 2 * cos x * x + Real.sqrt 6 * sin x * x

-- #runOnSympyExprAndCheckProofStxTest tan(tan(x) - sin(x)/cos(x)) -- OK
-- #runOnSympyExprAndCheckProofStxTest cos(pi/2 + x) -- OK
-- #runOnSympyExprAndCheckProofStxTest cos(-30*pi/2 + x) -- NOT OK
-- #runOnSympyExprAndCheckProofStxTest sin(x)/cos(x) -- OK

#parse_equalities Real.sin_antiperiodic



-- example (x : ℝ) : cos (Real.pi / 2 + x) = -sin x := by
--   grind [Real.cos_sq_add_sin_sq, Real.tan_eq_sin_div_cos, Real.sin_neg, Real.cos_neg, Real.sin_antiperiodic,
--     Real.cos_antiperiodic, Real.tan_periodic, Real.sin_periodic, Real.cos_periodic, Real.sin_zero, Real.cos_zero,
--     Real.tan_zero, Real.cos_sq', Real.sin_sq, Real.sin_pi_div_six, Real.cos_pi_div_six, Real.tan_pi_div_six,
--     Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.sin_pi_div_three, Real.cos_pi_div_three,
--     Real.tan_pi_div_three, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_sq_eq_half_sub, mul_sin_mul_cos,
--     mul_cos_mul_cos, mul_sin_mul_sin, Real.sin_add_sin, Real.sin_sub_sin, Real.cos_add_cos, Real.cos_sub_cos,
--     Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul, Real.cos_two_mul']

-- example (x : ℝ) : Real.sqrt 2 * cos x * x + Real.sqrt 6 * sin x * x = 2 * Real.sqrt 2 * x * sin (x + Real.pi / 6) := by
--   grind [Real.cos_sq_add_sin_sq, Real.tan_eq_sin_div_cos, Real.sin_neg, Real.cos_neg, Real.sin_antiperiodic,
--     Real.cos_antiperiodic, Real.tan_periodic, Real.sin_periodic, Real.cos_periodic, Real.sin_zero, Real.cos_zero,
--     Real.tan_zero, Real.cos_sq', Real.sin_sq, Real.sin_pi_div_six, Real.cos_pi_div_six, Real.tan_pi_div_six,
--     Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.sin_pi_div_three, Real.cos_pi_div_three,
--     Real.tan_pi_div_three, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_sq_eq_half_sub, mul_sin_mul_cos,
--     mul_cos_mul_cos, mul_sin_mul_sin, Real.sin_add_sin, Real.sin_sub_sin, Real.cos_add_cos, Real.cos_sub_cos,
--     Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul, Real.cos_two_mul']

-- example : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by grind
-- -- example (x : ℝ) : 1 - Real.cos (x) ^ 2 = Real.sin (x) ^ 2 := by
-- --   grind [Real.cos_sq_add_sin_sq, Real.tan_eq_sin_div_cos, Real.sin_neg, Real.cos_neg, Real.sin_antiperiodic,
-- --     Real.cos_antiperiodic, Real.tan_periodic, Real.sin_periodic, Real.cos_periodic, Real.sin_zero, Real.cos_zero,
-- --     Real.tan_zero, Real.cos_sq', Real.sin_sq, Real.sin_pi_div_six, Real.cos_pi_div_six, Real.tan_pi_div_six,
-- --     Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.sin_pi_div_three, Real.cos_pi_div_three,
-- --     Real.tan_pi_div_three, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_sq_eq_half_sub, mul_sin_mul_cos,
-- --     mul_cos_mul_cos, mul_sin_mul_sin, Real.sin_add_sin, Real.sin_sub_sin, Real.cos_add_cos, Real.cos_sub_cos,
-- --     Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul, Real.cos_two_mul',
-- --     Lean.Grind.Semiring.add_zero, Lean.Grind.Semiring.add_comm, Lean.Grind.Semiring.add_assoc,
-- --     Lean.Grind.Semiring.mul_assoc,
-- --     Lean.Grind.CommSemiring.mul_comm, Lean.Grind.Semiring.left_distrib,
-- --     Lean.Grind.Semiring.pow_succ,
-- --     Lean.Grind.Ring.neg_add_cancel, Lean.Grind.Ring.sub_eq_add_neg, Lean.Grind.Field.zpow_zero, mul_pow, pow_add,
-- --     Lean.Grind.Field.zpow_neg, neg_distrib, neg_comm]


-- example (x : ℝ) : 1 - Real.cos (x) ^ 2 = Real.sin (x) ^ 2 := by
--   grind [Real.cos_sq_add_sin_sq, Real.tan_eq_sin_div_cos, Real.sin_neg, Real.cos_neg, Real.sin_antiperiodic,
--     Real.cos_antiperiodic, Real.tan_periodic, Real.sin_periodic, Real.cos_periodic, Real.sin_zero, Real.cos_zero,
--     Real.tan_zero, Real.cos_sq', Real.sin_sq, Real.sin_pi_div_six, Real.cos_pi_div_six, Real.tan_pi_div_six,
--     Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.sin_pi_div_three, Real.cos_pi_div_three,
--     Real.tan_pi_div_three, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_sq_eq_half_sub, mul_sin_mul_cos,
--     mul_cos_mul_cos, mul_sin_mul_sin, Real.sin_add_sin, Real.sin_sub_sin, Real.cos_add_cos, Real.cos_sub_cos,
--     Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul, Real.cos_two_mul']
-- example : 1 + 1 = 2 := by grind
-- example : 1 - cos x ^ 2 = 1 - cos x ^ 2 := by grind


-- example (x : ℝ) : 1 - cos x ^ 2 = sin x ^ 2 := by grind [Real.cos_sq_add_sin_sq]
-- -- sin (x) ^ 2 * cos (-x + x) ^ 2

-- -- #runEggTestDirectional 0.5 + 0.5
-- -- #eval show MetaM Unit from do
-- --   let env ← getEnv
-- --   let categories := Parser.parserExtension.getState env |>.categories
-- --   for (name, _) in categories do
-- --     IO.println name
-- #eval Rat.ofScientific (2) true (1)
-- #eval (2 / 3 : ℚ).num
-- #eval (2 / 3 : ℚ).den
-- #runTestSuite "data/light.txt"
