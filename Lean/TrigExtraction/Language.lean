import Lean.Elab.Term
import Lean.PrettyPrinter
import TrigExtraction.Rules
open Lean Elab Term Meta PrettyPrinter

private opaque EGraph.Pointed : NonemptyType.{0}

def EGraph := EGraph.Pointed.type

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure EggResult where
  success : Bool
  term    : String
  egraph? : Option EGraph
  explanation : String
  log : String
deriving Inhabited

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure RewriteRule where
  name : String
  lhs  : String
  rhs  : String

structure DirectionalRewriteRule where
  name : String
  rule : String

inductive PrintType where
  | NormalExpr
  | Rule

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
  | NumLit (lit : String) : SymbolLang
  | Pi : SymbolLang
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
  | .NumLit _ => 1
  | .Pi => 1
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
  | .NumLit lit => lit
  | .Pi => "pi"
  | .Other o => o

-- partial def eggSyntaxToSymbolLang (stx : Syntax) : SymbolLang :=
--   match stx with
--   | `(term| $left + $right) =>




declare_syntax_cat egg_expr
syntax ident : egg_expr
syntax num : egg_expr
syntax str : egg_expr
syntax "(+ " egg_expr egg_expr ")" : egg_expr
syntax "(* " egg_expr egg_expr ")" : egg_expr
syntax "(- " egg_expr egg_expr ")" : egg_expr
syntax "(/ " egg_expr egg_expr ")" : egg_expr
syntax "(pow " egg_expr egg_expr ")" : egg_expr
syntax "(sin " egg_expr ")" : egg_expr
syntax "(cos " egg_expr ")" : egg_expr
syntax "(tan " egg_expr ")" : egg_expr
syntax "(sqrt " egg_expr ")" : egg_expr
syntax "(neg " egg_expr ")" : egg_expr
syntax "(inv " egg_expr ")" : egg_expr
syntax "pi" : egg_expr

partial def eggSyntaxToSymbolLang (stx : Syntax) : Except String SymbolLang :=
  match stx with
  | `(egg_expr| $id:ident) =>
    .ok (.Var id.getId.toString)

  | `(egg_expr| $n:num) =>
    .ok (.NumLit (toString n.getNat))

  | `(egg_expr| pi) =>
    .ok .Pi

  | `(egg_expr| (+ $left $right)) => do
    let leftAST ← eggSyntaxToSymbolLang left
    let rightAST ← eggSyntaxToSymbolLang right
    .ok (.Add leftAST rightAST)

  | `(egg_expr| (* $left $right)) => do
    let leftAST ← eggSyntaxToSymbolLang left
    let rightAST ← eggSyntaxToSymbolLang right
    .ok (.Mul leftAST rightAST)

  | `(egg_expr| (- $left $right)) => do
    let leftAST ← eggSyntaxToSymbolLang left
    let rightAST ← eggSyntaxToSymbolLang right
    .ok (.Sub leftAST rightAST)

  | `(egg_expr| (/ $left $right)) => do
    let leftAST ← eggSyntaxToSymbolLang left
    let rightAST ← eggSyntaxToSymbolLang right
    .ok (.Div leftAST rightAST)

  | `(egg_expr| (pow $base $exp)) => do
    let baseAST ← eggSyntaxToSymbolLang base
    let expAST ← eggSyntaxToSymbolLang exp
    .ok (.Pow baseAST expAST)

  | `(egg_expr| (neg $arg)) => do
    let argAST ← eggSyntaxToSymbolLang arg
    .ok (.Neg argAST)

  | `(egg_expr| (inv $arg)) => do
    let argAST ← eggSyntaxToSymbolLang arg
    .ok (.Inv argAST)

  | `(egg_expr| (sin $arg)) => do
    let argAST ← eggSyntaxToSymbolLang arg
    .ok (.Sin argAST)

  | `(egg_expr| (cos $arg)) => do
    let argAST ← eggSyntaxToSymbolLang arg
    .ok (.Cos argAST)

  | `(egg_expr| (tan $arg)) => do
    let argAST ← eggSyntaxToSymbolLang arg
    .ok (.Tan argAST)

  | `(egg_expr| (sqrt $arg)) => do
    let argAST ← eggSyntaxToSymbolLang arg
    .ok (.Sqrt argAST)

  | _ => .error s!"Unrecognized egg_expr syntax: {stx}"

-- TODO: convert to not use metaM
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
    return .Pi

  | `(term| $id:ident) =>
    let name := id.getId
    if name == `π || name == `Real.pi then
      return .Pi
    else
      return .Var name.toString

  | `(term| $n:num) =>
    return (.NumLit (toString n.getNat))

  | `(term| ($e)) =>
    syntaxToSymbolLang e

  -- | `(Real.termπ) =>
  --   return .Const .Pi

  | _ =>
    if stx.isOfKind `Real.termπ then
      return .Pi
    else
      let prettyStx ← ppTerm ⟨stx⟩
      return .Other (prettyStx.pretty)





-- TODO: convert to not use metaM
partial def symbolLangToSyntax (lang : SymbolLang) : MetaM (TSyntax `term) := do
  match lang with
  | .Var x =>
    let id := Lean.mkIdent x.toName
    return id

  | .NumLit c =>
    let n? := c.toNat?
    match n? with
    | some _ =>
      let numLit := Syntax.mkNumLit c
      return numLit
    | none =>
        throwError "Cannot convert constant {c} back to syntax"

  | .Pi =>
    `(term| Real.pi)

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

partial def symbolLangToExpr (lang : SymbolLang) : TermElabM Expr := do
  let stx ← symbolLangToSyntax lang
  let e ← elabTerm stx none
  return e

def ExprToString (e : Expr) : MetaM String := do
  let stx' ← delab e
  let l ← syntaxToSymbolLang stx'
  let s := SymbolLangToString l
  return s

def eggStringToStx (s : String) : MetaM Syntax := do
  let env ← getEnv
  match Parser.runParserCategory env `egg_expr s "<input>" with
  | .ok stx => return stx
  | .error msg => throwError s!"{msg}"

def eggStringToExpr (s : String) : TermElabM Expr := do
  logInfo m!"Received string {s} from Rust"
  let eggStx ← eggStringToStx s
  logInfo m!"Syntax is {eggStx}"
  let res := eggSyntaxToSymbolLang eggStx
  match res with
  | .ok l => do
      let e ← symbolLangToExpr l
      return e
  | .error msg => throwError msg
  -- logInfo m!"lang is {lang}"


inductive ParseResult where
  | success (name : Name) (lhs rhs : Expr)
  | failure (name : Name) (e : Expr) (reason : String)

inductive DirectedParseResult where
  | success (name : Name) (lhs rhs : Expr) (dir : Direction)
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

def parseDirectionalEqualitiesInt (directedEqs : (List (Name × Direction))) : MetaM (List DirectedParseResult) := do
  directedEqs.mapM fun directedEq =>
  do
    let (name, direction) := directedEq
    let result ← (parseEquality name)
    match result with
    | ParseResult.success name lhs rhs =>
      return DirectedParseResult.success name lhs rhs direction
    | ParseResult.failure name e reason =>
      return DirectedParseResult.failure name e reason


def parseDirectionalEqualities (directedEqs : List (Name × Direction)) : MetaM (Array DirectionalRewriteRule) := do
  let parsedDirectionalEqsList ← (parseDirectionalEqualitiesInt directedEqs)
  let mut successfulDirectedEqsList : List DirectionalRewriteRule := []
  for m in parsedDirectionalEqsList do
    match m with
    | DirectedParseResult.success name lhs rhs dir =>
        let lhsStr ← ExprToString lhs
        let rhsStr ← ExprToString rhs
        let s := match dir with
        | Direction.left_to_right => lhsStr ++ " => " ++ rhsStr
        | Direction.right_to_left => rhsStr ++ " => " ++ lhsStr
        | Direction.both => lhsStr ++ " <=> " ++ rhsStr
        successfulDirectedEqsList := successfulDirectedEqsList ++ [⟨name.toString, s⟩]
    | DirectedParseResult.failure _ _ _ => pure ()
  let successfulDirectedEqsArray := successfulDirectedEqsList.toArray
  return successfulDirectedEqsArray



-- todo: figure out why pi isn't parsed properly
