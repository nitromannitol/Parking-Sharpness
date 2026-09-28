import Parking.Support.NoArrivalFlag

/-!
# The arrival compensator

`arrivalCompensator` averages the departure counts of a matched pair of processes over the
neighbours of a site with `walkOp`, giving the conditional number of arrivals expected there
through a given round. This file collects its basic properties: nonnegativity, vanishing at
round zero, measurability in the round noise, the a priori box bound inherited from
`matchedOdometer_le_box`, the one-round recursion that adds a fresh count, and invariance
under overwriting instructions strictly after the round already accumulated.
-/

open LatticeProb (measurable_from_countable')

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The accumulated conditional entrance probabilities through a given round. -/
def arrivalCompensator (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ)
    (x : Site d) : ℝ :=
  walkOp (fun y => ((matchedState η ρ σ t).departures y : ℝ)) x

/-- The compensator is a `walkOp` average of nonnegative departure counts. -/
theorem arrivalCompensator_nonneg (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (x : Site d) : 0 ≤ arrivalCompensator η ρ σ t x := by
  rw [arrivalCompensator, walkOp_eq_nbrFinset]
  positivity

/-- At round zero every matched state is the initial one, with no departures yet. -/
theorem arrivalCompensator_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (x : Site d) : arrivalCompensator η ρ σ 0 x = 0 := by
  simp [arrivalCompensator, matchedState, initial, walkOp, nbrSum]

/-- The compensator is measurable in the round noise, via the measurability of
`matchedState`'s departure counts. -/
theorem measurable_arrivalCompensator (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    Measurable (fun σ : RoundNoise d => arrivalCompensator η ρ σ t x) := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id t
  simp only [arrivalCompensator, walkOp_eq_nbrFinset]
  exact (Finset.measurable_sum _ fun y _ =>
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 y)).div_const _

/-- The compensator inherits the box bound `matchedOdometer_le_box` through `walkOp`. -/
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
