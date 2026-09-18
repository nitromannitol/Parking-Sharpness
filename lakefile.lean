import Lake

open Lake DSL

package «parking_sharpness» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "b617769368d5cd11b5b2b43a16e72ff674da0a06"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «Parking» where
  globs := #[.andSubmodules `Parking]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

