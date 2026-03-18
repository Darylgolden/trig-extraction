import Lean
import TrigExtraction.Language
import TrigExtraction.Egg
import Lean.Elab.Tactic.Grind
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Lean Elab Term Meta PrettyPrinter
open Tactic


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
    let directed_rw_rules ← parseDirectionalEqualities combinedRulesDirectional
    let result ← runEggDirectional str directed_rw_rules
    logInfo m!"{result.term}"
    logInfo m!"Explanation: \n {result.explanation}"
    logInfo m!"Log: \n {result.log}"

elab "#runEggOnSympyExpr" stx:sympy_expr : command => do
  Command.runTermElabM fun _ => do
    let l ← parseSympy stx
    let str := SymbolLangToString l
    logInfo m!"Target parsed as {str}"
    let directed_rw_rules ← parseDirectionalEqualities combinedRulesDirectional
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

elab "#sympyToAST " t:sympy_expr : command => do
  Command.liftTermElabM do
    let ast ← parseSympy t
    logInfo m!"{repr ast}"


def tryProveWithGrind (goalType : Expr) (rules : List (Name × Direction)) : TermElabM (Option Expr) := do
  let mvar ← mkFreshExprMVar goalType (kind := .syntheticOpaque)
  let ruleNames := rules.map (·.1)
  let ruleSyntaxes ← ruleNames.toArray.mapM fun name => do
    let ident := mkIdent name
    `(Lean.Parser.Tactic.grindParam| $ident:ident)

  -- Re-enable the sepArray
  let sepArray := Syntax.TSepArray.ofElems ruleSyntaxes

  -- Interpolate the array directly into the block using the bracket spread syntax!
  let tacticStx ← `(tactic| grind [$sepArray,*])

  try
    -- Evaluate the tactic against the fresh goal
    let remaining ← Lean.Elab.Tactic.run mvar.mvarId! do
      Lean.Elab.Tactic.evalTactic tacticStx

    if remaining.isEmpty then
      return some mvar
    else
      logInfo m!"Grind left {remaining.length} unsolved goals"
      return none
  catch e =>
    logInfo m!"Grind threw error: {← e.toMessageData.toString}"
    return none



elab "#runOnSympyExprAndCheckProof" stx:sympy_expr : command => do
  Command.runTermElabM fun _ => do
    let l ← parseSympy stx
    let str := SymbolLangToString l
    logInfo m!"Target parsed as {str}"
    let directed_rw_rules ← parseDirectionalEqualities combinedRulesDirectional
    let result ← runEggDirectional str directed_rw_rules
    logInfo m!"{result.term}"
    logInfo m!"Explanation: \n {result.explanation}"
    logInfo m!"Log: \n {result.log}"

    -- logInfo m!"Explanation: {result.explanation}"

    if !result.success then
      logInfo "Egg failed to simplify"
      return


    let inputStx ← symbolLangToSyntax l
    let l' ← eggStringToSymbolLang result.term
    let outputStx ← symbolLangToSyntax l'
    let goalStx ← `(∀ (x : ℝ), $inputStx = $outputStx)
    let goal ← elabTerm goalStx none

    let proof? ← tryProveWithGrind goal combinedRulesDirectional

    match proof? with
    | some _ => logInfo m!"✓ Proved: {goal}"
    | none => logInfo m!"✗ Grind couldn't prove: {goal}"

elab "#runOnSympyExprAndCheckProofStx" stx:sympy_expr : command => do
  -- Run the simplification and syntax generation inside `liftTermElabM`
  -- This isolates the `TermElabM` constraints and lets us pull out the Syntaxes
  let stxPair? ← Command.liftTermElabM do
    let l ← parseSympy stx
    let str := SymbolLangToString l
    logInfo m!"Target parsed as {str}"

    let directed_rw_rules ← parseDirectionalEqualities combinedRulesDirectional
    let result ← runEggDirectional str directed_rw_rules
    logInfo m!"{result.term}"
    logInfo m!"Explanation: \n {result.explanation}"
    logInfo m!"Log: \n {result.log}"

    if !result.success then
      logInfo "Egg failed to simplify"
      return none

    let inputStx ← symbolLangToSyntax l
    let l' ← eggStringToSymbolLang result.term
    let outputStx ← symbolLangToSyntax l'

    return some (inputStx, outputStx)

  -- Now back in CommandElabM, build the full example theorem syntax and elaborate it!
  match stxPair? with
  | none => pure ()
  | some (inputStx, outputStx) =>
    -- Format our rules for the tactic explicitly
    let ruleNames := trigRulesDirectional.map (·.1)
    let ruleSyntaxes ← ruleNames.toArray.mapM fun name => do
      let ident := mkIdent name
      `(Lean.Parser.Tactic.grindParam| $ident:ident)

    let sepArray := Syntax.TSepArray.ofElems ruleSyntaxes

    -- Construct the exact command syntax that works perfectly as raw text
    let cmd ← `(example (x : ℝ) : $inputStx = $outputStx := by grind [$sepArray,*])
    logInfo m!"{cmd}"
    logInfo m!"Evaluating command directly..."
    -- Elaborate/Execute the command in the environment
    -- Get the message state explicitly from the CommandElabM environment
    let stateBefore ← get
    let msgsBefore := stateBefore.messages

    -- Elaborate/Execute the command in the environment
    Command.elabCommand cmd

    let stateAfter ← get
    let msgsAfter := stateAfter.messages

    -- Output any messages that were generated during elaboration
    let newMsgs := msgsAfter.unreported.toArray[msgsBefore.unreported.toArray.size:]
    for msg in newMsgs do
      -- Convert the raw MessageData to a String
      let msgString ← msg.data.toString
      logInfo m!"[Command Output]: {msgString}"

    if msgsAfter.hasErrors && !msgsBefore.hasErrors then
      logInfo m!"! Grind tactical failure. See the outputs above for context."
    else
      logInfo m!"✓ Proved successfully: {inputStx} = {outputStx}"

elab "#test_elab " stx:sympy_expr : command => do
  Command.runTermElabM fun _ => do
    let l ← parseSympy stx
    let inputExpr ← symbolLangToExpr l
    logInfo m!"inputExpr = {inputExpr}"
    let goal ← mkEq inputExpr inputExpr
    let proof? ← tryProveWithGrind goal trigRulesDirectional
    match proof? with
    | some _ => logInfo m!"Proved!"
    | none => logInfo m!"Failed!"

elab "#runOnSympyExprAndCheckProofStxTest" stx:sympy_expr : command => do
  Command.runTermElabM fun _ => do
    let l ← parseSympy stx
    let str := SymbolLangToString l
    logInfo m!"Target parsed as {str}"

    let directed_rw_rules ← parseDirectionalEqualities combinedRulesDirectional
    let result ← runEggDirectional str directed_rw_rules

    if !result.success then
      logInfo "Egg failed to simplify"
      return

    let inputStx ← symbolLangToSyntax l
    let l' ← eggStringToSymbolLang result.term
    let outputStx ← symbolLangToSyntax l'

    let ruleNames := trigRulesDirectional.map (·.1)
    let ruleSyntaxes ← ruleNames.toArray.mapM fun name => do
      let ident := mkIdent name
      `(Lean.Parser.Tactic.grindParam| $ident:ident)

    let sepArray := Syntax.TSepArray.ofElems ruleSyntaxes

    -- Combine the explicit type instantiation with the tactic block so they elaborate together!
    let fullProofStx ← `(show ∀ (x : ℝ), $inputStx = $outputStx by grind [$sepArray,*])

    logInfo m!"Evaluating full proof natively..."

    try
      -- Execute the entire proof natively, catching errors if `grind` fails
      let _proofExpr ← elabTerm fullProofStx none
      logInfo m!"{_proofExpr}"
      logInfo m!"✓ Proved successfully: {inputStx} = {outputStx}"
    catch e =>
      logWarning m!"✗ Grind failed or threw an error: {← e.toMessageData.toString}"
