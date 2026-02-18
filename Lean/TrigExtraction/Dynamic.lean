import TrigExtraction.Language
import Mathlib.Tactic.NormNum.Core
import Lean.Elab.Term

open Lean Elab Term Meta PrettyPrinter

def runNormNum (s : String) : TermElabM String := do
  let realType ← mkConst ``Real
  let e ← eggStringToExpr s (expectedType := some realType)

  let exprType ← inferType e
  unless ← isDefEq exprType realType do
    throwError "Expression must have type Real, but has type {exprType}"

  let result ← Mathlib.Meta.NormNum.eval e
  let normalizedExpr := result.expr
  let stx' ← delab normalizedExpr
  let l ← syntaxToSymbolLang stx'
  let str := SymbolLangToString l
  return str
