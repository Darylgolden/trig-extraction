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
-- 5
#check runEgg (toEggStringExpr (1 + 1)) rwRules
#runEgg (1)
#runEgg ((sin x)^2 + (cos x)^2)
