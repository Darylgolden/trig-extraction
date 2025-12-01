import Lean.Elab.Term
import Lean.PrettyPrinter
import TrigExtraction.Egg
open Lean Elab Term Meta PrettyPrinter

inductive PrintType where
  | NormalExpr
  | Rule

inductive SymbolLang where
  | Var (name : String) : SymbolLang
  | Add (left right : SymbolLang) : SymbolLang
  | Mul (left right : SymbolLang) : SymbolLang
  | Pow (left right : SymbolLang) : SymbolLang
  | Sin (arg : SymbolLang) : SymbolLang
  | Cos (arg : SymbolLang) : SymbolLang
  | Const (val : String) : SymbolLang
  | Other (stx : String) : SymbolLang
deriving Repr, BEq

def ASTSize (lang : SymbolLang) : Nat :=
  match lang with
  | .Var _ => 1
  | .Add left right => 1 + ASTSize left + ASTSize right
  | .Mul left right => 1 + ASTSize left + ASTSize right
  | .Pow base exponent => 1 + ASTSize base + ASTSize exponent
  | .Sin arg => 1 + ASTSize arg
  | .Cos arg => 1 + ASTSize arg
  | .Const _ => 1
  | .Other _ => 1

partial def TermCounter (t : Term) : Nat :=
  match t with
  | `(term| $left + $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left - $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left * $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left / $right) => 1 + TermCounter left + TermCounter right
  | `(term| $left ^ $right) => 1 + TermCounter left + TermCounter right
  | `(term| sin $arg) => 1 + TermCounter arg
  | `(term| cos $arg) => 1 + TermCounter arg
  | `(term| tan $arg) => 1 + TermCounter arg
  | `(term| ($subterm)) => TermCounter subterm
  | _ => 1

partial def LangToString (lang : SymbolLang) (typ : PrintType) : String :=
  match lang with
  | .Var x => match typ with
    | .NormalExpr => x
    | .Rule => s!"?{x}"
  | .Add left right => s!"(+ {LangToString left typ} {LangToString right typ})"
  | .Mul left right => s!"(* {LangToString left typ} {LangToString right typ})"
  | .Pow base exponent => s!"(pow {LangToString base typ} {LangToString exponent typ})"
  | .Sin arg => s!"(sin {LangToString arg typ})"
  | .Cos arg => s!"(cos {LangToString arg typ})"
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

  | `(term| $base ^ $exponent) =>
    let baseAST ← syntaxToSymbolLang base
    let exponentAST ← syntaxToSymbolLang exponent
    return .Pow baseAST exponentAST

  | `(term| sin $arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Sin argAST

  | `(term| cos $arg) =>
    let argAST ← syntaxToSymbolLang arg
    return .Cos argAST

  | `(term| $id:ident) =>
    return .Var id.getId.toString

  | `(term| $n:num) =>
    return .Const (toString n.getNat)

  | `(term| ($e)) =>
    syntaxToSymbolLang e

  | _ =>
    let prettyStx ← ppTerm ⟨stx⟩
    return .Other (prettyStx.pretty)

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
  let str := LangToString l PrintType.NormalExpr
  return mkStrLit str

elab "toEggStringRule" t:term : term => do
  let e ← elabTerm t none
  let stx' ← delab e
  let l ← syntaxToSymbolLang stx'
  let str := LangToString l PrintType.Rule
  return mkStrLit str


def rwRules : Array RewriteRule :=
  #[⟨"test", "(+ 1 1)", "2"⟩,
    -- ⟨"test2", "(+ (pow (sin ?x) 2) (pow (cos ?y) 2))", "1"⟩
    ]

elab "#runEgg" t:term : command => do
  Command.liftTermElabM do
    let e ← elabTerm t none
    let stx' ← delab e
    let l ← syntaxToSymbolLang stx'
    let str := LangToString l PrintType.NormalExpr
    let result ← runEgg str rwRules
    logInfo m!"{result.term}"
