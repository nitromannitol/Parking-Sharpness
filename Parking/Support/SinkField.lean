import Parking.Support.ClippedTable
import Parking.Support.HorizonSink
import Parking.Support.WeightedOdometerBounds

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The sparse field with a hole capacity that lasts through the specified horizon. -/
def sparseSinkField (T : ℕ) (v : Site d) (η : Site d → ℤ) : Site d → ℤ :=
  horizonSink (clippedField η) v T

theorem measurable_sparseSinkField (T : ℕ) (v : Site d) : Measurable (sparseSinkField T v) := by
  classical
  apply measurable_pi_lambda
  intro y
  by_cases hy : y = v
  · subst y
    simp only [sparseSinkField, horizonSink, Function.update_self]
    exact measurable_const
  · simpa only [sparseSinkField, horizonSink, Function.update_of_ne hy, Function.comp_def] using
      (measurable_pi_apply y).comp (measurable_clippedField (d := d))

theorem sparseSinkField_particle_bound (T : ℕ) (v : Site d) (η : Site d → ℤ) (y : Site d) :
    (sparseSinkField T v η y).toNat ≤ 1 :=
  horizonSink_particle_bound (clippedField η) v T (clippedField_particle_bound η) y

theorem sparseSinkField_le (T : ℕ) (v : Site d) (η : Site d → ℤ) (y : Site d) :
    sparseSinkField T v η y ≤ clippedField η y :=
  horizonSink_le (clippedField η) v T (clipSparse_bounds (η v)).1 y

theorem sparseSinkField_eq_of_ne (T : ℕ) (v : Site d) (η : Site d → ℤ) (y : Site d) (hy : y ≠ v) :
    sparseSinkField T v η y = clippedField η y := Function.update_of_ne hy _ _

/-- The sink field ignores the original count at its sink. -/
theorem sparseSinkField_update (T : ℕ) (v : Site d) (η : Site d → ℤ) (a : ℤ) :
    sparseSinkField T v (Function.update η v a) = sparseSinkField T v η := by
  classical
  funext y
  by_cases hy : y = v
  · subst y; simp [sparseSinkField, horizonSink]
  · simp [sparseSinkField, horizonSink, clippedField, hy]

/-- The sink can only reduce every odometer under the common table coupling. -/
theorem sparseSink_odometer_le (T : ℕ) (v : Site d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    (matchedState (sparseSinkField T v η) ρ σ t).departures x ≤
      (matchedState (clippedField η) ρ σ t).departures x :=
  (matched_counts_mono _ _ (sparseSinkField_le T v η) ρ ρ σ t).2.2 x

theorem sparseSink_mean_le (hd : 1 ≤ d) (T : ℕ) (v : Site d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    matchedMeanU (sparseSinkField T v η) ρ t x ≤ matchedMeanU (clippedField η) ρ t x :=
  integral_mono (integrable_matchedOdometer hd _ _ _ _) (integrable_matchedOdometer hd _ _ _ _)
    (fun σ => Nat.cast_le.mpr (sparseSink_odometer_le T v η ρ σ t x))

/-- The mean odometer at the sink is zero through its horizon. -/
theorem sparseSink_mean_zero (T : ℕ) (v : Site d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (t : ℕ) (ht : t ≤ T) :
    matchedMeanU (sparseSinkField T v η) ρ t v = 0 := by
  have hz (σ : RoundNoise d) : (matchedState (sparseSinkField T v η) ρ σ t).departures v = 0 :=
    (horizonSink_counts_zero (clippedField η) v T (clippedField_particle_bound η) ρ σ t ht).2
  simp only [matchedMeanU, hz, Nat.cast_zero, integral_zero]

/-- Outside the propagation box the sink has no effect on the conditional mean. -/
theorem sparseSink_mean_far (T : ℕ) (v : Site d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (x : Site d) (hx : x ∉ boxFinset v T) :
    matchedMeanU (sparseSinkField T v η) ρ T x = matchedMeanU (clippedField η) ρ T x := by
  apply matchedMeanU_agree_box
  intro y hy
  apply sparseSinkField_eq_of_ne
  intro he
  subst y
  apply hx
  rw [mem_boxFinset_iff] at hy ⊢
  intro i
  rw [abs_sub_comm]
  exact hy i
end Parking
