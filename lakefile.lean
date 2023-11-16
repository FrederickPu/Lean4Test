import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «lean4_test» {
  -- add package configuration options here
}

lean_lib «Lean4Test» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4_test» {
  root := `Main
}
