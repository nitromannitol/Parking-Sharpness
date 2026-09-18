import Parking.Support.MatchedBellman
import Parking.Support.Shells
import Parking.Support.Comparison

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- A translated box has the same cardinality as a box at the origin. -/
theorem card_boxFinset (x : Site d) (R : ℕ) : (boxFinset x R).card = (2 * R + 1) ^ d := by
  classical
  have he : (boxFinset (0 : Site d) R).image (fun y => x + y) = boxFinset x R := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_boxFinset_iff] at hz ⊢
      intro i
      simpa using hz i
    · intro hy
      refine ⟨y - x, ?_, by abel⟩
      rw [mem_boxFinset_iff] at hy ⊢
      intro i
      simpa using hy i
  rw [← he, Finset.card_image_of_injective _ (fun y z h => add_left_cancel h)]
  exact card_boxFinset_zero R

/-- A bounded initial particle count gives a uniform finite bound at every site. -/
theorem matchedCount_le_box (η : Site d → ℤ) (K : ℕ) (hη : ∀ y, (η y).toNat ≤ K)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    matchedCount η ρ σ t x ≤ (2 * t + 1) ^ d * K := by
  calc
    _ ≤ (candidates η x t).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ∑ y ∈ boxFinset x t, (η y).toNat := card_candidates_le η x t
    _ ≤ ∑ _y ∈ boxFinset x t, K := Finset.sum_le_sum fun y _ => hη y
    _ = _ := by simp [card_boxFinset]

/-- The corresponding uniform odometer bound, with no condition on the initial holes. -/
theorem matchedOdometer_le_box (η : Site d → ℤ) (K : ℕ) (hη : ∀ y, (η y).toNat ≤ K)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    (matchedState η ρ σ T).departures x ≤ T * ((2 * T + 1) ^ d * K) := by
  apply (matchedOdometer_le_candidates η ρ σ T x).trans
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∑ y ∈ boxFinset x T, (η y).toNat := card_candidates_le η x T
    _ ≤ ∑ _y ∈ boxFinset x T, K := Finset.sum_le_sum fun y _ => hη y
    _ = _ := by simp [card_boxFinset]
end Parking
