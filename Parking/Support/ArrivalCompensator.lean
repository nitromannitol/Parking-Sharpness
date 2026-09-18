import Parking.Support.NoArrivalFlag

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The accumulated conditional entrance probabilities through a given round. -/
def arrivalCompensator (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) : ℝ :=
  walkOp (fun y => ((matchedState η ρ σ t).departures y : ℝ)) x

theorem arrivalCompensator_nonneg (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (x : Site d) : 0 ≤ arrivalCompensator η ρ σ t x := by
  rw [arrivalCompensator, walkOp_eq_nbrFinset]
  positivity

theorem arrivalCompensator_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (x : Site d) :
    arrivalCompensator η ρ σ 0 x = 0 := by
  simp [arrivalCompensator, matchedState, initial, walkOp, nbrSum]

theorem measurable_arrivalCompensator (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    Measurable (fun σ : RoundNoise d => arrivalCompensator η ρ σ t x) := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id t
  simp only [arrivalCompensator, walkOp_eq_nbrFinset]
  exact (Finset.measurable_sum _ fun y _ =>
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 y)).div_const _

theorem arrivalCompensator_bound (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    arrivalCompensator η ρ σ t x ≤ ((t * ((2 * t + 1) ^ d * K) : ℕ) : ℝ) :=
  walkOp_le_of_nbr hd (fun y _ => Nat.cast_le.mpr (matchedOdometer_le_box η K hη ρ σ t y))

/-- A fresh round adds the conditional number of entrances from its active particles. -/
theorem arrivalCompensator_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    arrivalCompensator η ρ σ (t + 1) x = arrivalCompensator η ρ σ t x +
      walkOp (fun y => (matchedCount η ρ σ t y : ℝ)) x := by
  have he (y : Site d) : ((matchedState η ρ σ (t + 1)).departures y : ℝ) =
      ((matchedState η ρ σ t).departures y : ℝ) + (matchedCount η ρ σ t y : ℝ) := Nat.cast_add _ _
  simp only [arrivalCompensator, walkOp_eq_nbrFinset, he, Finset.sum_add_distrib, add_div]

/-- Future instructions cannot change the compensator accumulated so far. -/
theorem arrivalCompensator_update (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (n t : ℕ) (τ : RoundSlot d → Fin d × Bool) (ht : t ≤ n) (x : Site d) :
    arrivalCompensator η ρ (Function.update σ n τ) t x = arrivalCompensator η ρ σ t x := by
  unfold arrivalCompensator
  rw [matchedState_update η ρ σ n t τ ht]
end Parking
