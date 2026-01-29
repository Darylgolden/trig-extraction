import TrigExtraction.Language
import Mathlib.Tactic.NormNum.Core
import Lean.Elab.Term

open Lean Elab Term Meta PrettyPrinter

def runNormNum (s : String) : TermElabM String := do
  let e ← eggStringToExpr s
  let e ← instantiateMVars e  -- Instantiate all metavariables
  synthesizeSyntheticMVarsNoPostponing  -- Ensure type class instances are synthesized
  let e ← instantiateMVars e  -- Instantiate again after synthesis
  let result ← Mathlib.Meta.NormNum.eval e
  let e := result.expr
  let stx' ← delab e
  let l ← syntaxToSymbolLang stx'
  let str := SymbolLangToString l
  return str
