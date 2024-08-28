import Lake
open Lake DSL

package "InfiniteGaloisTheory" where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


lean_lib «InfiniteGaloisTheory» where
  -- add library configuration options here

@[default_target]
lean_exe "infinitegaloistheory" where
  root := `Main

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"