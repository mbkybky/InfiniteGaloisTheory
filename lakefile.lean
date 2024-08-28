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
