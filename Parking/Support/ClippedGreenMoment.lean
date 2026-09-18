import Parking.Support.ClippedMoments
import Parking.Support.BoundedConditionalMoment
import Parking.Support.HalfMoment
import Parking.Support.WeightedMoment
import Parking.Support.WeightedOdometerBounds

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The instruction variance moment is bounded by a dimension-dependent multiple of the odometer norm. -/
theorem exists_clipped_green_moment_bound (hd : 5 ≤ d) :
    ∃ W : ℝ, 0 < W ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
      (∫ z, greenWeightedOdometer (clippedField z.1) 0 (curryRoundNoise z.2) T x T ^ (r / 2)
        ∂((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d))) ^ (1 / r) ≤
        Real.sqrt (W * rNorm ((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) r (clippedTableU T 0)) := by
  obtain ⟨W, hW, hsum⟩ := exists_greenSquareWeight_sum_bound hd
  refine ⟨W, hW, fun p hp hp4 T x r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)
  let S := boxFinset x T
  let w : Site d → ℝ := fun v => walkOp (fun y => fullGreen d (y - x) ^ 2) v
  let M := ∫ z, clippedTableU T 0 z ^ (r / 2) ∂μ
  have hM : 0 ≤ M := integral_nonneg fun z => Real.rpow_nonneg (clippedTableU_nonneg T 0 z) _
  have hi (v : Site d) : Integrable (fun z => clippedTableU T v z ^ (r / 2)) μ :=
    integrable_rpow_bounded_nonneg μ _ (measurable_clippedTableU hd1 T v)
      (clippedTableU_nonneg T v) _ (fun z => (le_abs_self _).trans (clippedTableU_bound T v z)) (by linarith)
  have hweighted := integral_weighted_rpow_le μ S w (clippedTableU T)
    (fun v _ => greenSquareWeight_nonneg x v) (fun v _ => clippedTableU_nonneg T v)
    (fun v _ => measurable_clippedTableU hd1 T v) (by linarith : 1 ≤ r / 2)
    (fun v _ => hi v) M hM
    (fun v _ => le_of_eq (integral_clippedTableU_rpow_shift hd1 hp hp4 T v (by linarith)))
  have hW0 : 0 ≤ ∑ v ∈ S, w v := Finset.sum_nonneg fun v _ => greenSquareWeight_nonneg x v
  have hbound : (∫ z, greenWeightedOdometer (clippedField z.1) 0 (curryRoundNoise z.2) T x T ^ (r / 2) ∂μ) ≤
      W ^ (r / 2) * M := by
    exact hweighted.2.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hW0 (hsum x S) (by linarith)) hM)
  have hXhalf := integrable_abs_rpow_bounded μ (clippedTableU T 0) (measurable_clippedTableU hd1 T 0)
    _ (clippedTableU_bound T 0) (by linarith : 0 ≤ r / 2)
  have hXfull := integrable_abs_rpow_bounded μ (clippedTableU T 0) (measurable_clippedTableU hd1 T 0)
    _ (clippedTableU_bound T 0) (by linarith : 0 ≤ r)
  exact half_moment_root_le μ (clippedTableU T 0) (clippedTableU_nonneg T 0)
    (measurable_clippedTableU hd1 T 0) hr hXhalf hXfull hW.le
    (integral_nonneg fun z => Real.rpow_nonneg (greenWeightedOdometer_nonneg _ _ _ _ _ _) _) hbound
end Parking
