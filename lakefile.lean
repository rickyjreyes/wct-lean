import Lake
open Lake DSL

package my_project where
  version := v!"0.1.0"

@[default_target]
lean_lib MyProject

lean_exe my_project where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"
