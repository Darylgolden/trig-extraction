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
#eval syntaxToAST 0.5 + 0.5
#eval syntaxToAST (1/2) + (1/2)
#eval syntaxToAST 0.23
#runEggTestDirectional sin ( x ) ^ 2 * cos ( -x + x ) ^ 2
-- sin (x) ^ 2 * cos (-x + x) ^ 2

-- #runEggTestDirectional 0.5 + 0.5
-- #eval show MetaM Unit from do
--   let env ← getEnv
--   let categories := Parser.parserExtension.getState env |>.categories
--   for (name, _) in categories do
--     IO.println name
#eval Rat.ofScientific (2) true (1)
#eval (2 / 3 : ℚ).num
#eval (2 / 3 : ℚ).den
