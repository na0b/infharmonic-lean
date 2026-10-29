import Lake
open Lake DSL

package «infharmonic» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «InfHarmonic» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0-rc2"

lean_lib «Challenge» where
  roots := #[`Challenge]

lean_lib «Solution» where
  roots := #[`Solution]
