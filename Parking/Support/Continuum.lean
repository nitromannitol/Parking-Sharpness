/-
The continuum objects of Section 8 of `parking.tex`: test functions on
`R^d` and on space-time, the operator `L = (2d)^{-1}Δ`, spatial white noise,
and the rescaled lattice fields of `prop:spatial-scaling`.

- `IsTestFun φ` is `φ ∈ C_c^∞(R^d)` and `IsSpaceTimeTest ψ` is
  `ψ ∈ C_c^∞((0,∞) × R^d)`.
- `pairing f φ` is `∫ f φ`, and `contOp d` is `L = (2d)^{-1}Δ`.
- `IsSpatialWhiteNoise d v μ W` says that `W` is a mean-zero spatial white
  noise of intensity `v`: linear in the test function, with mean zero, with
  covariance `v ∫ φψ`, and with Gaussian one-dimensional marginals.
- `latticePoint R x` is the coordinatewise floor `⌊Rx⌋`, `barOdometer` and
  `barDivisible` are the rescaled odometers
  `R^{d/2-2}U_{⌊sR^2⌋}(⌊Rx⌋)` and `R^{d/2-2}u_{⌊sR^2⌋}(⌊Rx⌋)`, and
  `scenePair`, `signedPair` are the pairings `⟨η_R,φ⟩` and `⟨ν_R,φ⟩`.

`IsTestFun`, `IsSpaceTimeTest`, `contOp` and `IsSpatialWhiteNoise` are defined in the
library (`LatticeProb/WhiteNoise.lean`) and exported into `Parking`, where the frozen
statements name them.
-/
import Parking.Support.Range
import LatticeProb.WhiteNoise

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parking

export LatticeProb.WhiteNoise (IsTestFun IsSpaceTimeTest contOp IsSpatialWhiteNoise)

/-- The coordinatewise floor `⌊Rx⌋`. -/
def latticePoint {d : ℕ} (R : ℝ) (x : Fin d → ℝ) : Site d := fun i => ⌊R * x i⌋

/-- `R^{d/2-2}U_{⌊sR^2⌋}(⌊Rx⌋)`. -/
def barOdometer {d : ℕ} (ω : Data d) (R : ℝ) (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  R ^ ((d : ℝ) / 2 - 2) * (U ω ⌊s * R ^ 2⌋₊ (latticePoint R x) : ℝ)

/-- `R^{d/2-2}u_{⌊sR^2⌋}(⌊Rx⌋)`. -/
def barDivisible {d : ℕ} (ω : Data d) (R : ℝ) (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  R ^ ((d : ℝ) / 2 - 2) * uOf ω ⌊s * R ^ 2⌋₊ (latticePoint R x)

/-- `⟨η_R, φ⟩ = R^{-d/2}∑_y η(y)φ(y/R)`. -/
def scenePair {d : ℕ} (ω : Data d) (R : ℝ) (φ : (Fin d → ℝ) → ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2) * ∑' y : Site d, (ω.1 y : ℝ) * φ fun i => (y i : ℝ) / R

/-- `⟨ν_R, φ⟩ = R^{-d/2}∑_y (A_{⌊R^2⌋}(y)-H_{⌊R^2⌋}(y))φ(y/R)`. -/
def signedPair {d : ℕ} (ω : Data d) (R : ℝ) (φ : (Fin d → ℝ) → ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2) * ∑' y : Site d,
    ((A ω ⌊R ^ 2⌋₊ y : ℝ) - (H ω ⌊R ^ 2⌋₊ y : ℝ)) * φ fun i => (y i : ℝ) / R

end Parking

end
