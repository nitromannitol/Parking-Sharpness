import Lake

open Lake DSL

package «parking_sharpness» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "d36783565c4de41cce5cf079ddd5ace3efe6a8ff"

require «divisible_sandpile» from git
  "https://github.com/nitromannitol/Divisible-Sandpile-Percolation.git" @
    "c8f92874d75cfa86140a2eae2fa0fad7559b9d26"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

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
