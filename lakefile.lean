import Lake

open Lake DSL

package «parking_sharpness» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "4012b5c7662714883d248e2352ad1c6382dc49dd"

require «divisible_sandpile» from git
  "https://github.com/nitromannitol/Divisible-Sandpile-Percolation.git" @
    "cd8b15a32d00b1eec48f8747339e2d0cfaa73a21"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- The comparator audit surface (`ParkingAudit/*/Challenge.lean`,
`ParkingAudit/*/SolutionBasic.lean`, `ParkingAudit/*/Solution.lean` and `ParkingAudit/Support/`).
Not a default target: it builds only on demand (`lake build ParkingAudit`), so the ordinary build
of `Parking` is unchanged. -/
lean_lib «ParkingAudit» where
  globs := #[.submodules `ParkingAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

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
