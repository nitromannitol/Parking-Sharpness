import Parking.Support.HorizonSink
import Parking.Support.RoundMeanField
import Parking.Support.DiscrepancyMeas

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Hole counts can only decrease from their initial value. -/
theorem matchedHoles_le_initial (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    (matchedState η ρ σ t).holes x ≤ (-η x).toNat := by
  induction t with
  | zero => rfl
  | succ t ih => rw [matchedHoles_succ]; exact (Nat.sub_le _ _).trans ih

/-- Bounded initial particles give integrable active counts under every finite table measure. -/
theorem integrable_matchedCount_bounded (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d)
    (μ : Measure (RoundNoise d)) [IsFiniteMeasure μ] :
    Integrable (fun σ => (matchedCount η ρ σ t x : ℝ)) μ := by
  have hm := measurable_matchedCount ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id t
  apply Integrable.of_bound ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
    ((measurable_pi_apply x).comp hm)).aestronglyMeasurable (((2 * t + 1) ^ d * K : ℕ) : ℝ)
  exact ae_of_all _ fun σ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (matchedCount_le_box η K hη ρ σ t x)

/-- A fixed site's hole count is integrable without any uniform assumption on the other holes. -/
theorem integrable_matchedHoles (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (t : ℕ) (x : Site d) (μ : Measure (RoundNoise d)) [IsFiniteMeasure μ] :
    Integrable (fun σ => ((matchedState η ρ σ t).holes x : ℝ)) μ := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id t
  apply Integrable.of_bound ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
    (hS.2.2.1 x)).aestronglyMeasurable ((-η x).toNat : ℝ)
  exact ae_of_all _ fun σ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (matchedHoles_le_initial η ρ σ t x)

/-- Physical arrivals and the incoming table entries have equal counts. -/
theorem card_matchedArrivals_eq_countArrivals (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    (matchedArrivals η ρ σ t x).card = (countArrivals (matchedCount η ρ σ t) (σ t) x).card := by
  rw [card_matchedArrivals]
  rfl

theorem measurable_card_matchedArrivals (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    Measurable (fun σ : RoundNoise d => ((matchedArrivals η ρ σ t x).card : ℝ)) := by
  simp_rw [card_matchedArrivals_eq_countArrivals]
  exact (measurable_from_countable' fun s : Finset (RoundSlot d) => (s.card : ℝ)).comp
    (measurable_countArrivals (fun σ => matchedCount η ρ σ t) (fun σ => σ t)
      (measurable_matchedCount ⟨0, hd⟩ (fun _ => η) (fun _ => ρ) id
        measurable_const measurable_const measurable_id t) (measurable_pi_apply t) x)

/-- The physical arrival count is integrable for every bounded particle field. -/
theorem integrable_matchedArrivals_bounded (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d)
    (μ : Measure (RoundNoise d)) [IsFiniteMeasure μ] :
    Integrable (fun σ => ((matchedArrivals η ρ σ t x).card : ℝ)) μ := by
  apply Integrable.of_bound (measurable_card_matchedArrivals hd η ρ t x).aestronglyMeasurable
    (((2 * (t + 1) + 1) ^ d * K : ℕ) : ℝ)
  exact ae_of_all _ fun σ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (matchedArrivals_le_box η K hη ρ σ t x)
end Parking
