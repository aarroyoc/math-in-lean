import Lake
open Lake DSL

package «math-in-lean» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MathInLean» {
  -- add any library configuration options here
}
