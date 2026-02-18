import Lean
import TrigExtraction.Language
import TrigExtraction.Egg
open Lean Elab Term Meta PrettyPrinter


elab "termMatch" t:term : term => do
  return mkNatLit (TermCounter t)

elab "showRawElab " t:term : term => do
  let e ← elabTerm t none
  logInfo m!"{repr e}"
  return mkStrLit (toString (repr e))

elab "rawElabSize" t: term : term => do
  let e ← elabTerm t none
  return mkNatLit e.sizeWithoutSharing

elab "syntaxToAST " t:term : term => do
  let ast ← syntaxToSymbolLang t
  return mkStrLit (toString (repr ast))

elab "exprSyntaxToAST " t:term : term => do
  let e ← elabTerm t none
  let stx' ← delab e
  let ast ← syntaxToSymbolLang stx'
  return mkStrLit (toString (repr ast))

elab "getASTSize" t:term : term => do
  let e ← elabTerm t none
  let stx' ← delab e
  let ast ← syntaxToSymbolLang stx'
  let size := ASTSize ast
  return mkNatLit size

elab "toEggStringExpr" t:term : term => do
  let e ← elabTerm t none
  let stx' ← delab e
  let l ← syntaxToSymbolLang stx'
  let str := SymbolLangToString l
  return mkStrLit str

elab "toEggStringRule" t:term : term => do
  let e ← elabTerm t none
  let stx' ← delab e
  let l ← syntaxToSymbolLang stx'
  let str := SymbolLangToString l
  return mkStrLit str


-- def rwRules : Array RewriteRule :=
--   #[⟨"test", "(+ 1 1)", "2"⟩,
--     ⟨"test2", "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))", "1"⟩
--     ]

-- elab "#runEgg" t:term : command => do
--   Command.runTermElabM fun _ => do
--     let e ← elabTerm t none
--     let stx' ← delab e
--     let l ← syntaxToSymbolLang stx'
--     let str := SymbolLangToString l
--     let result ← runEgg str rwRules
--     logInfo m!"{result.term}"

elab "#runEggTest" t:term : command => do
  Command.runTermElabM fun _ => do
    let e ← elabTerm t none
    let stx' ← delab e
    let l ← syntaxToSymbolLang stx'
    let str := SymbolLangToString l
    logInfo m!"Target parsed as {str}"
    let rw_rules ← parseEqualities trigRules
    for rule in rw_rules do
      logInfo m!"Rule: {rule.name}: {rule.lhs} => {rule.rhs}"
    let result ← runEgg str rw_rules
    logInfo m!"{result.term}"
    logInfo m!"Explanation: \n {result.explanation}"

elab "#runEggTestDirectional" t:term : command => do
  Command.runTermElabM fun _ => do
    logInfo m!"test"
    let e ← elabTerm t none
    let stx' ← delab e
    let l ← syntaxToSymbolLang stx'
    let str := SymbolLangToString l
    logInfo m!"Target parsed as {str}"
    let directed_rw_rules ← parseDirectionalEqualities trigRulesDirectional
    let result ← runEggDirectional str directed_rw_rules
    logInfo m!"{result.term}"
    logInfo m!"Explanation: \n {result.explanation}"
    logInfo m!"Log: \n {result.log}"

elab "#printASTSize" t:term : command => do
  Command.runTermElabM fun _ => do
    let e ← elabTerm t none
    logInfo m!"Expr: {e}"
    let stx' ← delab e
    logInfo m!"Delaborated Syntax: {stx'}"
    logInfo m!"Syntax repr: {repr stx'}"
    -- Check if it matches patterns
    match stx' with
    | `(term| Real.pi) => logInfo m!"Matched Real.pi pattern"
    | `(term| $id:ident) => logInfo m!"Matched ident pattern: {id.getId}"
    | _ => logInfo m!"No pattern matched"
    let l ← syntaxToSymbolLang stx'
    let size := ASTSize l
    logInfo m!"AST: {repr l}"
    logInfo m!"AST Size: {size}"

elab "#print_lhs_rhs " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  Command.liftTermElabM do
    let info ← getConstInfo name
    let type := info.type
    match type.eq? with
    | some (_, lhs, rhs) =>
      logInfo m!"Theorem: {name}\n {lhs} = {rhs}"
    | none =>
      logError m!"{name} is not an equality. It is {type}"

elab "#print_lhs_rhs_metavars" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  Command.liftTermElabM fun _ => do
    let info ← getConstInfo name
    let type := info.type
    let (args, _, conclusion) ← forallMetaTelescope type
    logInfo m!"args is {args} and conclusion is {conclusion}"

elab "#parse_equalities " ids:ident+ : command => do
  let eqs ← Command.liftTermElabM do
    ids.toList.mapM fun id => do
      let name ← resolveGlobalConstNoOverload id.raw
      return name
  Command.liftTermElabM do
    let results ← parseEqualitiesInt eqs
    for result in results do
      match result with
      | ParseResult.success name lhs rhs =>
        logInfo m!"[OK] {name}: LHS: {lhs} RHS: {rhs}"
      | ParseResult.failure name e reason =>
        logWarning m!"[WARN] {name} failed to parse; expr is {e}, reason: {reason}"
