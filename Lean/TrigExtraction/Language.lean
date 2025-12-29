import Lean.Elab.Term
import Lean.PrettyPrinter
import TrigExtraction.Egg
import TrigExtraction.Rules
open Lean Elab Term Meta PrettyPrinter

inductive PrintType where
  | NormalExpr
  | Rule

-- need to modify const so it takes symbol lang instead of string.
-- want something like const (5) but also const (5 + 5)

inductive SymbolLang where
  | Var (name : String) : SymbolLang
  | Add (left right : SymbolLang) : SymbolLang
  | Mul (left right : SymbolLang) : SymbolLang
  | Sub (left right : SymbolLang) : SymbolLang
  | Div (left right : SymbolLang) : SymbolLang
  | Neg (arg : SymbolLang) : SymbolLang
  | Inv (arg : SymbolLang) : SymbolLang
  | Pow (left right : SymbolLang) : SymbolLang
  | Sin (arg : SymbolLang) : SymbolLang
  | Cos (arg : SymbolLang) : SymbolLang
  | Tan (arg : SymbolLang) : SymbolLang
  | Sqrt (arg : SymbolLang) : SymbolLang
  | Const (val : String) : SymbolLang
  | Other (stx : String) : SymbolLang
deriving Repr, BEq

def ASTSize (lang : SymbolLang) : Nat :=
  match lang with
  | .Var _ => 1
  | .Add left right => 1 + ASTSize left + ASTSize right
  | .Mul left right => 1 + ASTSize left + ASTSize right
  | .Sub left right => 1 + ASTSize left + ASTSize right
  | .Div left right => 1 + ASTSize left + ASTSize right
  | .Neg arg => 1 + ASTSize arg
  | .Inv arg => 1 + ASTSize arg
  | .Pow base exponent => 1 + ASTSize base + ASTSize exponent
  | .Sin arg => 1 + ASTSize arg
  | .Cos arg => 1 + ASTSize arg
  | .Tan arg => 1 + ASTSize arg
  | .Sqrt arg => 1 + ASTSize arg
  | .Const _ => 1
  | .Other _ => 1

partial def TermCounter (t : Term) : Nat :=
  match t with
  | `(term| $left + $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left - $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left * $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left / $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left ^ $right) => 1 + TermCounter left + TermCounter right
  | `(term| -$arg) => 1 + TermCounter arg
  | `(term| $arg⁻¹) => 1 + TermCounter arg
  | `(term| sin $arg) => 1 + TermCounter arg
  | `(term| cos $arg) => 1 + TermCounter arg
  | `(term| tan $arg) => 1 + TermCounter arg
  | `(term| Real.sqrt $arg) => 1 + TermCounter arg
  | `(term| Real.pi) => 1
  | `(term| ($subterm)) => TermCounter subterm
  | _ => 1

-- partial def LangToString (lang : SymbolLang) (typ : PrintType) : String :=
--   match lang with
--   | .Var x => match typ with
--     | .NormalExpr => x
--     | .Rule => s!"?{x}"
--   | .Add left right => s!"(+ {LangToString left typ} {LangToString right typ})"
--   | .Mul left right => s!"(* {LangToString left typ} {LangToString right typ})"
--   | .Pow base exponent => s!"(pow {LangToString base typ} {LangToString exponent typ})"
--   | .Sin arg => s!"(sin {LangToString arg typ})"
--   | .Cos arg => s!"(cos {LangToString arg typ})"
--   | .Const c => c
--   | .Other o => o

partial def SymbolLangToString (lang : SymbolLang) : String :=
  match lang with
  | .Var x => x
  | .Add left right => s!"(+ {SymbolLangToString left} {SymbolLangToString right})"
  | .Mul left right => s!"(* {SymbolLangToString left} {SymbolLangToString right})"
  | .Sub left right => s!"(- {SymbolLangToString left} {SymbolLangToString right})"
  | .Div left right => s!"(/ {SymbolLangToString left} {SymbolLangToString right})"
  | .Pow base exponent => s!"(pow {SymbolLangToString base} {SymbolLangToString exponent})"
  | .Neg arg => s!"(neg {SymbolLangToString arg})"
  | .Inv arg => s!"(inv {SymbolLangToString arg})"
  | .Sin arg => s!"(sin {SymbolLangToString arg})"
  | .Cos arg => s!"(cos {SymbolLangToString arg})"
  | .Tan arg => s!"(tan {SymbolLangToString arg})"
  | .Sqrt arg => s!"(sqrt {SymbolLangToString arg})"
  | .Const c => c
  | .Other o => o

partial def syntaxToSymbolLang (stx : Syntax) : MetaM SymbolLang := do
  match stx with
  | `(term| $left + $right) =>
    let leftAST ← syntaxToSymbolLang left
    let rightAST ← syntaxToSymbolLang right
    return .Add leftAST rightAST

  | `(term| $left * $right) =>
    let leftAST ← syntaxToSymbolLang left
    let rightAST ← syntaxToSymbolLang right
    return .Mul leftAST rightAST

  | `(term| $left - $right) =>
    let leftAST ← syntaxToSymbolLang left
    let rightAST ← syntaxToSymbolLang right
    return .Sub leftAST rightAST

  | `(term | $left / $right) =>
    let leftAST ← syntaxToSymbolLang left
    let rightAST ← syntaxToSymbolLang right
    return .Div leftAST rightAST

  | `(term| $base ^ $exponent) =>
    let baseAST ← syntaxToSymbolLang base
    let exponentAST ← syntaxToSymbolLang exponent
    return .Pow baseAST exponentAST

  | `(term| -$arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Neg argAST

  | `(term| $arg⁻¹) =>
    let argAST ← syntaxToSymbolLang arg
    return .Inv argAST

  | `(term| sin $arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Sin argAST

  | `(term| cos $arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Cos argAST

  | `(term| tan $arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Tan argAST

  | `(term| Real.sqrt $arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Sqrt argAST

  | `(term| Real.pi) =>
    return .Const "pi"

  | `(term| $id:ident) =>
    return .Var id.getId.toString

  | `(term| $n:num) =>
    return .Const (toString n.getNat)

  | `(term| ($e)) =>
    syntaxToSymbolLang e

  | _ =>
    let prettyStx ← ppTerm ⟨stx⟩
    return .Other (prettyStx.pretty)


partial def symbolLangToSyntax (lang : SymbolLang) : MetaM (TSyntax `term) := do
  match lang with
  | .Var x =>
    let id := Lean.mkIdent x.toName
    return id

  | .Const c =>
    let n? := c.toNat?
    match n? with
    | some n =>
      let numLit := Syntax.mkNumLit c
      return numLit
    | none =>
      if c == "pi" then
        `(term| Real.pi)
      else
        throwError "Cannot convert constant {c} back to syntax"

  | .Add left right =>
    let leftStx ← symbolLangToSyntax left
    let rightStx ← symbolLangToSyntax right
    `(term| $leftStx + $rightStx)

  | .Mul left right =>
    let leftStx ← symbolLangToSyntax left
    let rightStx ← symbolLangToSyntax right
    `(term| $leftStx * $rightStx)

  | .Sub left right =>
    let leftStx ← symbolLangToSyntax left
    let rightStx ← symbolLangToSyntax right
    `(term| $leftStx - $rightStx)

  | .Div left right =>
    let leftStx ← symbolLangToSyntax left
    let rightStx ← symbolLangToSyntax right
    `(term| $leftStx / $rightStx)

  | .Pow base exponent =>
    let baseStx ← symbolLangToSyntax base
    let exponentStx ← symbolLangToSyntax exponent
    `(term| $baseStx ^ $exponentStx)

  | .Neg arg =>
    let argStx ← symbolLangToSyntax arg
    `(term| -$argStx)

  | .Inv arg =>
    let argStx ← symbolLangToSyntax arg
    `(term| $argStx⁻¹)

  | .Sin arg =>
    let argStx ← symbolLangToSyntax arg
    `(term| Real.sin ($argStx))

  | .Cos arg =>
    let argStx ← symbolLangToSyntax arg
    `(term| Real.cos ($argStx))

  | .Tan arg =>
    let argStx ← symbolLangToSyntax arg
    `(term| Real.tan ($argStx))

  | .Sqrt arg =>
    let argStx ← symbolLangToSyntax arg
    `(term| Real.sqrt ($argStx))

  | .Other o =>
    throwError "Cannot convert Other node back to syntax: {o}"

def ExprToString (e : Expr) : MetaM String := do
  let stx' ← delab e
  let l ← syntaxToSymbolLang stx'
  let s := SymbolLangToString l
  return s

inductive ParseResult where
  | success (name : Name) (lhs rhs : Expr)
  | failure (name : Name) (e : Expr) (reason : String)

def parseEqualityExpr (name : Name) (e : Expr) : MetaM (ParseResult) := do
  let (_, _, conclusion) ← forallMetaTelescope e
  match conclusion.eq? with
  | some (_, lhs, rhs) => return ParseResult.success name lhs rhs
  | none => return ParseResult.failure name conclusion "some reason"

def parseEquality (name : Name) : MetaM (ParseResult) := do
  let info ← getConstInfo name
  let type := info.type
  parseEqualityExpr name type

def parseEqualitiesInt (eqs : List Name) : MetaM (List ParseResult) := do
  eqs.mapM fun name =>
    parseEquality name

def parseEqualities (eqs : List Name) : MetaM (Array RewriteRule) := do
  let parsedEqsList ← (parseEqualitiesInt eqs)
  let mut successfulEqsList : List RewriteRule := []
  for m in parsedEqsList do
    match m with
    | ParseResult.success name lhs rhs =>
      let lhsStr ← ExprToString lhs
      let rhsStr ← ExprToString rhs
      successfulEqsList := successfulEqsList ++ [⟨name.toString, lhsStr, rhsStr⟩]
    | ParseResult.failure _ _ _ => pure ()
  let successfulEqsArray := successfulEqsList.toArray
  return successfulEqsArray


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


def rwRules : Array RewriteRule :=
  #[⟨"test", "(+ 1 1)", "2"⟩,
    ⟨"test2", "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))", "1"⟩
    ]

elab "#runEgg" t:term : command => do
  Command.runTermElabM fun _ => do
    let e ← elabTerm t none
    let stx' ← delab e
    let l ← syntaxToSymbolLang stx'
    let str := SymbolLangToString l
    let result ← runEgg str rwRules
    logInfo m!"{result.term}"

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
