import Parking.Support.ClippedMoments
import Parking.Support.SceneryCenter
import Parking.Support.ProductLift
import Parking.Support.WeightedOdometerBounds

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The initial-field part of the odometer norm is its mean plus a Gaussian moment error. -/
theorem exists_clipped_scenery_norm_bound (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
      rNorm (iidLaw d (threePointLaw p)) r (fun η => matchedMeanU (clippedField η) 0 T x) ≤
        meanU (law d (threePointLaw p)) T + C * Real.sqrt r := by
  obtain ⟨C, hC, hsg⟩ := exists_sparse_scenery_moment hd
  refine ⟨C, hC, fun p hp hp4 T x r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hr0 : 0 < r := by linarith
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  let μ := iidLaw d (threePointLaw p)
  let m := meanU (law d (threePointLaw p)) T
  let M : (Site d → ℤ) → ℝ := fun η => matchedMeanU (clippedField η) 0 T x
  let F : (Site d → ℤ) → ℝ := fun η => M η - m
  let B : ℝ := ((T * (2 * T + 1) ^ d : ℕ) : ℝ)
  have hm0 : 0 ≤ m := integral_nonneg fun _ => Nat.cast_nonneg _
  have hM : Measurable M := (measurable_matchedMeanU hd1 0 T x).comp measurable_clippedField
  have hMB (η : Site d → ℤ) : |M η| ≤ B := by
    rw [abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
    simpa only [mul_one] using matchedMeanU_le_box hd1 (clippedField η) 1
      (clippedField_particle_bound η) 0 T x
  have hFB (η : Site d → ℤ) : |F η| ≤ B + |m| := by
    calc
      _ ≤ |M η| + |-m| := abs_add_le _ _
      _ ≤ B + |m| := by rw [abs_neg]; exact add_le_add (hMB η) le_rfl
  have heint := integral_matchedMeanU_eq_meanU hd1 (threePointLaw p) (integrable_threePointLaw p _) T x
  have he : F =ᵐ[μ] (fun η => matchedMeanU η 0 T x - ∫ ζ, matchedMeanU ζ 0 T x ∂μ) := by
    filter_upwards [ae_clippedField (threePointLaw p) (ae_clipSparse_threePointLaw p)] with η hη
    change matchedMeanU (clippedField η) 0 T x - m = _
    rw [hη, heint]
  have hFn : rNorm μ r F ≤ C * Real.sqrt r := by
    rw [rNorm_congr_ae μ r he]
    exact (hsg p hp hp4 T x r hr).2
  have hadd := rNorm_bounded_add_le μ (by linarith : 1 ≤ r) F (fun _ => m)
    (hM.sub_const m) measurable_const (B + |m|) |m| hFB (fun _ => le_rfl)
  have heF : (fun η => F η + m) = M := funext fun _ => sub_add_cancel _ _
  rw [heF, rNorm_const μ hr0 hm0] at hadd
  exact hadd.trans (by linarith)
end Parking
