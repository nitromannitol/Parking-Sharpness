/-
`thm:nearest` from the clauses of `prop:spatial-scaling` and ONE PATHWISE
statement.

`Parking.nearest_of_spatial_data` reduced `parking.tex:1807-1833` to the
continuum statement (S), which asks for a deterministic test function and a
deterministic level.  `Parking.exists_signed_level_of_pathwise` produces both
from the pathwise positivity of the continuum signed pair, so what `thm:nearest`
now rests on, besides the frozen clauses of `prop:spatial-scaling`, is the single
sample-by-sample identity of `parking.tex:1813-1814`:

  for every nonnegative test function `φ` whose support lies in the set where
  `U(1,·) > 0`,   `⟨W,φ⟩ + ∫ U(1,x) (Lφ)(x) dx > 0`,

which the paper obtains from the distributional equation on `O` by mollifying in
time on the RIGHT of `s = 1` and using the monotonicity of `U` in `s`.
-/
import Parking.Support.NearestSpatialAssembly
import Parking.Support.NearestTestFun

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology

variable {d : ℕ}

/-- **`thm:nearest` from the frozen clauses and the pathwise positivity of the
continuum signed pair.** -/
theorem nearest_of_pathwise_signed (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) [IsProbabilityMeasure (law d ν)]
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hUm : ∀ s x, Measurable fun ω => Uc ω s x)
    (hct : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hFDD : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
        (sp : Fin k → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ l, IsTestFun (χ l)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction
          ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2,
              fun j => barOdometer w R (sp j).1 (sp j).2,
              fun l => signedPair w R (χ l)) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun l => W (χ l) ω
                + ∫ x, Uc ω 1 x * contOp d (χ l) x) ∂Q)))
    (hclose : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ η : ℝ, 0 < η →
      Tendsto (fun R : ℝ => ((law d ν) {w | η < ⨆ p ∈ K,
          |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal) atTop (𝓝 0))
    (htight : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ η : ℝ, 0 < η →
      ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ((law d ν) {w | η < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    (hpos0 : ∀ᵐ ω ∂Q, 0 < Uc ω 1 0)
    (hWm : ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ →
      Measurable fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x)
    (hid : ∀ᵐ ω ∂Q, ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ → (∀ x, 0 ≤ φ x) → φ 0 = 1 →
      (∀ x ∈ tsupport φ, 0 < Uc ω 1 x) →
      0 < W φ ω + ∫ x, Uc ω 1 x * contOp d φ x) :
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal) atTop (𝓝 0) :=
  nearest_of_spatial_data hd ν hprob Q W Uc hUm hct hFDD hclose htight hpos0
    (fun _r₀ hr₀ _ε hε =>
      exists_signed_level_of_pathwise Q W Uc hWm
        (ae_exists_pos_l1_ball Q Uc hct hpos0) hid hr₀ hε)

end Parking
end
