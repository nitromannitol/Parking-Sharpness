import Parking.Support.MatchedCounts

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The candidate set increases with the allowed travel time. -/
theorem candidates_mono_time (η : Site d → ℤ) (x : Site d) {s t : ℕ} (hst : s ≤ t) :
    candidates η x s ⊆ candidates η x t := by
  classical
  unfold candidates
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (boxFinset_mono hst)

/-- At a fixed site and finite horizon, the common-table odometer has a deterministic finite bound. -/
theorem matchedOdometer_le_candidates (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    (matchedState η ρ σ T).departures x ≤ T * (candidates η x T).card := by
  have hsum : ∀ t, (matchedState η ρ σ t).departures x = ∑ s ∈ Finset.range t, matchedCount η ρ σ s x := by
    intro t
    induction t with
    | zero => simp [matchedState, initial]
    | succ t ih =>
        change (matchedState η ρ σ t).departures x + matchedCount η ρ σ t x = _
        rw [Finset.sum_range_succ, ih]
  rw [hsum]
  calc
    ∑ s ∈ Finset.range T, matchedCount η ρ σ s x ≤ ∑ _s ∈ Finset.range T, (candidates η x T).card := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.card_le_card
      exact (Finset.filter_subset _ _).trans (candidates_mono_time η x (by simpa using (Finset.mem_range.mp hs).le))
    _ = T * (candidates η x T).card := by simp

/-- Conditional on any initial field and priorities, every finite-horizon odometer is integrable. -/
theorem integrable_matchedOdometer (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    Integrable (fun σ => ((matchedState η ρ σ T).departures x : ℝ)) (roundNoiseLaw d) := by
  haveI := roundNoiseLaw_isProbability hd
  have hS := measurableState_matchedState ⟨0, hd⟩ (Ω := RoundNoise d)
    (fun _ => η) (fun _ => ρ) id measurable_const measurable_const measurable_id T
  apply Integrable.of_bound ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
    (hS.2.2.2 x)).aestronglyMeasurable ((T * (candidates η x T).card : ℕ) : ℝ)
  apply ae_of_all
  intro σ
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change ((matchedState η ρ σ T).departures x : ℝ) ≤ ((T * (candidates η x T).card : ℕ) : ℝ)
  exact_mod_cast matchedOdometer_le_candidates η ρ σ T x
end Parking
