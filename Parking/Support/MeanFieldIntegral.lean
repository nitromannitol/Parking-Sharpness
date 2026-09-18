import Parking.Support.WeightedOdometerBounds
import Parking.Support.SceneryCenter
import Parking.Support.ClippedTable
import Parking.Support.WalkIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Conditional mean odometers of a bounded measurable random field are integrable. -/
theorem integrable_matchedMeanU_bounded (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Φ : Ω → Site d → ℤ) (hΦ : Measurable Φ)
    (K : ℕ) (hΦb : ∀ ω y, (Φ ω y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    Integrable (fun ω => matchedMeanU (Φ ω) ρ T x) μ := by
  apply Integrable.of_bound ((measurable_matchedMeanU hd ρ T x).comp hΦ).aestronglyMeasurable
    ((T * ((2 * T + 1) ^ d * K) : ℕ) : ℝ)
  exact ae_of_all _ fun ω => by
    change ‖matchedMeanU (Φ ω) ρ T x‖ ≤ ((T * ((2 * T + 1) ^ d * K) : ℕ) : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
    exact matchedMeanU_le_box hd (Φ ω) K (hΦb ω) ρ T x

/-- The walk average of finitely many integrable functions is integrable. -/
theorem integrable_walkOp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Site d → ℝ) (x : Site d) (hi : ∀ y ∈ nbrFinset x, Integrable (fun ω => f ω y) μ) :
    Integrable (fun ω => walkOp (f ω) x) μ := by
  simp only [walkOp_eq_nbrFinset]
  exact (integrable_finsetSum _ hi).div_const _

/-- The clipped conditional mean has the common scalar mean of the original sparse process. -/
theorem integral_clipped_matchedMeanU (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) :
    ∫ η, matchedMeanU (clippedField η) 0 T x ∂(iidLaw d (threePointLaw p)) =
      meanU (law d (threePointLaw p)) T := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  have he : (fun η => matchedMeanU (clippedField η) 0 T x) =ᵐ[iidLaw d (threePointLaw p)]
      (fun η => matchedMeanU η 0 T x) :=
    (ae_clippedField (threePointLaw p) (ae_clipSparse_threePointLaw p)).mono
      fun η hη => congrArg (fun ζ => matchedMeanU ζ 0 T x) hη
  rw [integral_congr_ae he]
  exact integral_matchedMeanU_eq_meanU hd _ (integrable_threePointLaw p _) T x
end Parking
