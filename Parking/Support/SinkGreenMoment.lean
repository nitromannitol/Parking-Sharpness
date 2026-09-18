import Parking.Support.SinkObservable
import Parking.Support.BoundedConditionalMoment
import Parking.Support.WeightedOdometerBounds

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Killing at a sink reduces the entire Green-weighted odometer. -/
theorem sparseSink_greenWeighted_le (T : ℕ) (v x : Site d) (η : Site d → ℤ) (σ : RoundNoise d) :
    greenWeightedOdometer (sparseSinkField T v η) 0 σ T x T ≤
      greenWeightedOdometer (clippedField η) 0 σ T x T := by
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (sparseSink_odometer_le T v η 0 σ T y))
    (greenSquareWeight_nonneg x y)

/-- The half-moment of the sink variance is bounded by that of the ordinary process. -/
theorem sparseSink_green_moment_le (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℕ) (v x : Site d) {r : ℝ} (hr : 0 < r) :
    (∫ z, greenWeightedOdometer (sparseSinkField T v z.1) 0 (curryRoundNoise z.2) T x T ^ (r / 2)
      ∂((iidLaw d ν).prod (flatRoundNoiseLaw d))) ^ (1 / r) ≤
      (∫ z, greenWeightedOdometer (clippedField z.1) 0 (curryRoundNoise z.2) T x T ^ (r / 2)
        ∂((iidLaw d ν).prod (flatRoundNoiseLaw d))) ^ (1 / r) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  let μ := (iidLaw d ν).prod (flatRoundNoiseLaw d)
  let Q : (Site d → ℤ) × FlatRoundNoise d → ℝ := fun z =>
    greenWeightedOdometer (clippedField z.1) 0 (curryRoundNoise z.2) T x T
  have hQ : Measurable Q := Finset.measurable_sum _ fun y _ => (measurable_clippedTableU hd T y).const_mul _
  have hQ0 (z : (Site d → ℤ) × FlatRoundNoise d) : 0 ≤ Q z := greenWeightedOdometer_nonneg _ _ _ _ _ _
  have hQB (z : (Site d → ℤ) × FlatRoundNoise d) : Q z ≤
      (∑ y ∈ boxFinset x T, walkOp (fun w => fullGreen d (w - x) ^ 2) y) * ((T * (2 * T + 1) ^ d : ℕ) : ℝ) :=
    greenWeightedOdometer_le_box _ (clippedField_particle_bound z.1) 0 _ T x T
  have hi := integrable_rpow_bounded_nonneg μ Q hQ hQ0 _ hQB (by linarith : 0 ≤ r / 2)
  apply Real.rpow_le_rpow (integral_nonneg fun z => Real.rpow_nonneg (greenWeightedOdometer_nonneg _ _ _ _ _ _) _) _ (by positivity)
  apply integral_mono_of_nonneg (ae_of_all _ fun z => Real.rpow_nonneg (greenWeightedOdometer_nonneg _ _ _ _ _ _) _) hi
  exact ae_of_all _ fun z => Real.rpow_le_rpow (greenWeightedOdometer_nonneg _ _ _ _ _ _)
    (sparseSink_greenWeighted_le T v x z.1 (curryRoundNoise z.2)) (by linarith)
end Parking
