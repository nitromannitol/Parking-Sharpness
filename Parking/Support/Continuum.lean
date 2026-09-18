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
-/
import Parking.Support.Range

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parking

/-- A test function on `R^d`. -/
def IsTestFun {d : ℕ} (φ : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- A test function on `(0,∞) × R^d`. -/
def IsSpaceTimeTest {d : ℕ} (ψ : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ ∀ p ∈ tsupport ψ, 0 < p.1

/-- The pairing `⟨f, φ⟩ = ∫ f φ`. -/
def pairing {d : ℕ} (f φ : (Fin d → ℝ) → ℝ) : ℝ := ∫ x, f x * φ x

/-- The Laplacian of a smooth function on `R^d`. -/
def lap {d : ℕ} (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, deriv (fun s => deriv (fun t => φ (Function.update x i t)) s) (x i)

/-- `L = (2d)^{-1}Δ`. -/
def contOp (d : ℕ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := lap φ x / (2 * d)

/-- `W` is a mean-zero spatial white noise of intensity `v`. -/
def IsSpatialWhiteNoise (d : ℕ) (v : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) : Prop :=
  (∀ φ ψ : (Fin d → ℝ) → ℝ, IsTestFun φ → IsTestFun ψ → ∀ a b : ℝ,
      W (fun x => a * φ x + b * ψ x) =ᵐ[μ] fun ω => a * W φ ω + b * W ψ ω) ∧
  (∀ φ, IsTestFun φ → Integrable (W φ) μ ∧ ∫ ω, W φ ω ∂μ = 0) ∧
  (∀ φ ψ, IsTestFun φ → IsTestFun ψ →
      Integrable (fun ω => W φ ω * W ψ ω) μ ∧
      ∫ ω, W φ ω * W ψ ω ∂μ = v * ∫ x, φ x * ψ x) ∧
  (∀ φ, IsTestFun φ → ∃ s : NNReal, (s : ℝ) = v * ∫ x, φ x ^ 2 ∧
      μ.map (W φ) = ProbabilityTheory.gaussianReal 0 s)

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
