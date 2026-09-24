import Lake

open Lake DSL

package «parking_sharpness» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "bbe0b90a7cf0517db0578139aaab7f152edbc45e"

require «divisible_sandpile» from git
  "https://github.com/nitromannitol/Divisible-Sandpile-Percolation.git" @
    "679a368eb89b0b4188c0bea9bf8799db2055fd31"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

/-- The comparator audit surface (`Audit/*/Challenge.lean`, `Audit/*/Solution.lean` and
`Audit/Support/`).  Not a default target: it builds only on demand (`lake build Audit`), so the
ordinary build of `Parking` is unchanged. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]
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
