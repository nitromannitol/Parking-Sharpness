import Lake

open Lake DSL

package «parking_sharpness» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "7ab7f25507502a17bd1d71220bc1862804162c64"

require «divisible_sandpile» from git
  "https://github.com/nitromannitol/Divisible-Sandpile-Percolation.git" @
    "58c21b8399823c3b5d1208608ceeac2ce5cefb5d"

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
