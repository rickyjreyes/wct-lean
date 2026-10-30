import Lake
open Lake DSL

package my_project where
  version := v!"0.1.0"

@[default_target]
lean_lib MyProject

@[default_target]
lean_lib WCTLean

lean_exe my_project where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

-- The math package has its Lake root in the lean/ subdirectory.
-- Pinned to a concrete revision, never a floating branch.
require reyes_math from git
  "https://github.com/rickyjreyes/math" @ "afa8c27db10e9eff54f4dbb3e8e2d9530d042542" / "lean"
