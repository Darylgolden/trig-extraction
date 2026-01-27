import Lean

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

-- example : 2 + 2 = 4 := by norm_num
