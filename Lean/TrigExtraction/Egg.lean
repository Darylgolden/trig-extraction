import Lean
import TrigExtraction.Dynamic
import TrigExtraction.Language
open Lean Elab Term Meta PrettyPrinter


@[extern "run_egg_c"]
opaque runEgg (target : String) (rws : Array RewriteRule) : TermElabM EggResult

@[extern "run_egg_directional_c"]
opaque runEggDirectional (target : String) (directedRws : Array DirectionalRewriteRule) : TermElabM EggResult

def runEggSafe (target : String) (rws : Array RewriteRule) : TermElabM (Except String EggResult) := do
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
def callNormNumSafe (eggExpr : String) : TermElabM (Except String String) := do
  try
    IO.println "Hello world!"
    let result ← runNormNum eggExpr
    return Except.ok result
  catch e =>
    return Except.error (← e.toMessageData.toString)

-- def sayHi (name : String) : String :=
--   s!"Hello {name}!"

-- example : 2 + 2 = 4 := by norm_num
