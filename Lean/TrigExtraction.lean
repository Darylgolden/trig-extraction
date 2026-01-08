import TrigExtraction.Basic
import TrigExtraction.Egg
import TrigExtraction.Language
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

#parse_equalities Real.sin_add
#runEggTest ((cos x)^2 + (sin x)^2)
#runEggTest x + 0
#runEggTest x + 1
#runEggTest (1 - (sin x)^2)
#runEggTest sin ((1 + x) - x)^2 + (cos (1))^2
#runEggTest (1 + x) - x
#runEggTest (sin x) * (sin x) * (sin x) * (sin x)
-- #runEggTest Real.pi
-- #printASTSize Real.pi
-- #printASTSize 1
