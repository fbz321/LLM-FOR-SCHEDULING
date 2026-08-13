import Lake
open Lake DSL

package «OnlineScheduling» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «OnlineScheduling» where

lean_exe "onlinescheduling" where
  root := `Main
