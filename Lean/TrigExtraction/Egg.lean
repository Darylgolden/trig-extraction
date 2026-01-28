import Lean
import TrigExtraction.Dynamic
import TrigExtraction.Language
open Lean Elab Term Meta PrettyPrinter


@[extern "run_egg_c"]
opaque runEgg (target : String) (rws : Array RewriteRule) : Lean.MetaM EggResult

@[extern "run_egg_directional_c"]
opaque runEggDirectional (target : String) (directedRws : Array DirectionalRewriteRule) : Lean.MetaM EggResult

def runEggSafe (target : String) (rws : Array RewriteRule) : Lean.MetaM (Except String EggResult) := do
  let result ← runEgg target rws
  if result.success then
    return Except.ok result
  else
    return Except.error result.explanation

@[extern "query_egraph"]
opaque EGraph.query (egraph : EGraph) (query : String) : EggResult

def EGraph.querySafe (egraph : EGraph) (query : String) : Except String EggResult :=
  let result := EGraph.query egraph query
  if result.success then
    Except.ok result
  else
    Except.error result.explanation

@[export transfer_string]
def sayHi (name : String) : String :=
  s!"Hello {name}!"

def callNormNum (eggExpr : String) : TermElabM String :=
  (runNormNum eggExpr)



-- example : 2 + 2 = 4 := by norm_num
