import Lake

open Lake DSL

package «parking_sharpness» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "9d44b4d4670df393bb86ac5a4e042f215001cddf"

require «divisible_sandpile» from git
  "https://github.com/nitromannitol/Divisible-Sandpile-Percolation.git" @
    "cd8b15a32d00b1eec48f8747339e2d0cfaa73a21"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

/-- The comparator audit surface (`ParkingAudit/*/Challenge.lean`, `ParkingAudit/*/Solution.lean`
and `ParkingAudit/Support/`).  Not a default target: it builds only on demand
(`lake build ParkingAudit`), so the ordinary build of `Parking` is unchanged. -/
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
