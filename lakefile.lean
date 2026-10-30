import Lake
open Lake DSL

package «R3BiotSavartStream»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

@[default_target]
lean_lib «R3BiotSavartStream» where
  roots := #[`R3BiotSavartStream]
