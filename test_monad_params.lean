import Lean
open Lean Elab Term Meta

-- Test function to see how many parameters TermElabM expects in FFI
@[extern "test_termelabm_c"]
opaque testTermElabM : TermElabM Unit

-- Test function to see how many parameters MetaM expects in FFI
@[extern "test_metam_c"]
opaque testMetaM : MetaM Unit

-- Check the types
#check testTermElabM
#check testMetaM
