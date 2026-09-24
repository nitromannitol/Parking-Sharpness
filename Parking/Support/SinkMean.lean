import Parking.Support.SinkField
import Parking.Support.MeanFieldIntegral
import Parking.Support.MeanLaplacianOrder
import Parking.Support.ExteriorBarrier

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The expected odometer of the sparse process killed at the origin through the given horizon. -/
def sparseSinkMean (p : ℝ) (T : ℕ) (x : Site d) : ℝ :=
  ∫ η, matchedMeanU (sparseSinkField T 0 η) 0 T x ∂(iidLaw d (threePointLaw p))

theorem sparseSinkMean_nonneg (p : ℝ) (T : ℕ) (x : Site d) : 0 ≤ sparseSinkMean p T x :=
  integral_nonneg fun _ => matchedMeanU_nonneg _ _ _ _

theorem sparseSinkMean_zero (p : ℝ) (T : ℕ) : sparseSinkMean (d := d) p T 0 = 0 := by
  simp only [sparseSinkMean, sparseSink_mean_zero T 0 _ 0 T le_rfl, integral_zero]

/-- The sink mean is no greater than the stationary mean without a sink. -/
theorem sparseSinkMean_le (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) : sparseSinkMean p T x ≤ meanU (law d (threePointLaw p)) T := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  have h := integral_mono
    (integrable_matchedMeanU_bounded hd (iidLaw d (threePointLaw p)) (sparseSinkField T 0)
      (measurable_sparseSinkField T 0) 1 (sparseSinkField_particle_bound T 0) 0 T x)
    (integrable_matchedMeanU_bounded hd (iidLaw d (threePointLaw p)) clippedField
      measurable_clippedField 1 clippedField_particle_bound 0 T x)
    (fun η => sparseSink_mean_le hd T 0 η 0 T x)
  rw [integral_clipped_matchedMeanU hd hp hp4 T x] at h
  exact h

/-- Finite propagation makes the sink mean exactly stationary outside the horizon box. -/
theorem sparseSinkMean_far (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) (hx : x ∉ boxFinset 0 T) :
    sparseSinkMean p T x = meanU (law d (threePointLaw p)) T := by
  unfold sparseSinkMean
  simp_rw [sparseSink_mean_far T 0 _ 0 x hx]
  exact integral_clipped_matchedMeanU hd hp hp4 T x

/-- The expected sink odometer is superharmonic away from its absorbing site. -/
theorem sparseSinkMean_superharmonic (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) (hx : x ≠ 0) : walkOp (sparseSinkMean p T) x ≤ sparseSinkMean p T x := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  let μ := iidLaw d (threePointLaw p)
  let f : (Site d → ℤ) → Site d → ℝ := fun η => matchedMeanU (sparseSinkField T 0 η) 0 T
  let g : (Site d → ℤ) → Site d → ℝ := fun η => matchedMeanU (clippedField η) 0 T
  have hfi (y : Site d) : Integrable (fun η => f η y) μ :=
    integrable_matchedMeanU_bounded hd μ (sparseSinkField T 0) (measurable_sparseSinkField T 0)
      1 (sparseSinkField_particle_bound T 0) 0 T y
  have hgi (y : Site d) : Integrable (fun η => g η y) μ :=
    integrable_matchedMeanU_bounded hd μ clippedField measurable_clippedField 1 clippedField_particle_bound 0 T y
  have hpt (η : Site d → ℤ) : walkOp (f η) x - f η x ≤ walkOp (g η) x - g η x :=
    matchedMeanU_laplacian_mono hd _ _ (sparseSinkField_le T 0 η) 1 (clippedField_particle_bound η)
      0 T x (sparseSinkField_eq_of_ne T 0 η x hx)
  have h := integral_mono ((integrable_walkOp μ f x (fun y _ => hfi y)).sub (hfi x))
    ((integrable_walkOp μ g x (fun y _ => hgi y)).sub (hgi x)) hpt
  change (∫ η, walkOp (f η) x - f η x ∂μ) ≤ (∫ η, walkOp (g η) x - g η x ∂μ) at h
  rw [integral_sub (integrable_walkOp μ f x (fun y _ => hfi y)) (hfi x),
    integral_sub (integrable_walkOp μ g x (fun y _ => hgi y)) (hgi x),
    integral_walkOp μ f x (fun y _ => hfi y), integral_walkOp μ g x (fun y _ => hgi y)] at h
  have he (y : Site d) : (∫ η, g η y ∂μ) = meanU (law d (threePointLaw p)) T :=
    integral_clipped_matchedMeanU hd hp hp4 T y
  simp_rw [he] at h
  rw [walkOp_const hd, sub_self] at h
  exact sub_nonpos.mp h

/-- The mean sink odometer dominates the Green escape barrier. -/
theorem sparseSinkMean_green_lower (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) :
    meanU (law d (threePointLaw p)) T * (1 - srwGreenInf d x / srwGreenInf d 0) ≤ sparseSinkMean p T x :=
  exterior_superharmonic_barrier hd _ _ (integral_nonneg fun _ => Nat.cast_nonneg _)
    (sparseSinkMean_zero p T) (fun y hy => sparseSinkMean_superharmonic (by omega) hp hp4 T y hy)
    T (fun y hy => sparseSinkMean_far (by omega) hp hp4 T y hy) x
end Parking
