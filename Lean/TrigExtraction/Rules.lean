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
