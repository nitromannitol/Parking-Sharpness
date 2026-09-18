import Parking.Support.GreenSquareSum
import Parking.Support.MatchedUniform
import Parking.Support.FlatNoise
import Parking.Support.TableQuadratic

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Averaging preserves the deterministic bounded-count odometer estimate. -/
theorem matchedMeanU_le_box (hd : 1 ≤ d) (η : Site d → ℤ) (N : ℕ)
    (hη : ∀ y, (η y).toNat ≤ N) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    matchedMeanU η ρ T x ≤ ((T * ((2 * T + 1) ^ d * N) : ℕ) : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  have h := integral_mono (integrable_matchedOdometer hd η ρ T x)
    (integrable_const ((T * ((2 * T + 1) ^ d * N) : ℕ) : ℝ))
    (fun σ => Nat.cast_le.mpr (matchedOdometer_le_box η N hη ρ σ T x))
  simpa only [matchedMeanU, integral_const, probReal_univ, one_smul] using h

/-- The finite Green-weighted odometer is bounded for every bounded particle field. -/
theorem greenWeightedOdometer_le_box (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) (x : Site d) (R : ℕ) :
    greenWeightedOdometer η ρ σ T x R ≤
      (∑ v ∈ boxFinset x R, walkOp (fun y => fullGreen d (y - x) ^ 2) v) * ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  unfold greenWeightedOdometer
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (greenSquareWeight_nonneg x v)
  exact_mod_cast (by simpa only [mul_one] using matchedOdometer_le_box η 1 hη ρ σ T v)

/-- The finite Green-weighted odometer is measurable in the flattened table. -/
theorem measurable_greenWeightedOdometer (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (R : ℕ) :
    Measurable (fun ω : FlatRoundNoise d => greenWeightedOdometer η ρ (curryRoundNoise ω) T x R) := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : FlatRoundNoise d => η)
    (fun _ => ρ) curryRoundNoise measurable_const measurable_const measurable_curryRoundNoise T
  exact Finset.measurable_sum _ fun v _ =>
    (((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 v)).const_mul _)
end Parking
