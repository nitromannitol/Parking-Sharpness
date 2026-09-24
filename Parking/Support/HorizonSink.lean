import Parking.Support.MatchedUniform
import Parking.Support.MatchedMonotone

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- The arriving particles at a site come from its finite initial propagation box. -/
theorem matchedArrivals_le_box (η : Site d → ℤ) (K : ℕ) (hη : ∀ y, (η y).toNat ≤ K)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    (matchedArrivals η ρ σ t x).card ≤ (2 * (t + 1) + 1) ^ d * K := by
  calc
    _ ≤ (candidates η x (t + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ∑ y ∈ boxFinset x (t + 1), (η y).toNat := card_candidates_le η x (t + 1)
    _ ≤ ∑ _y ∈ boxFinset x (t + 1), K := Finset.sum_le_sum fun y _ => hη y
    _ = _ := by simp [card_boxFinset]

/-- Up to a fixed horizon, a hole can lose only the bounded number of possible arrivals per round. -/
theorem matchedHoles_loss_le (η : Site d → ℤ) (K : ℕ) (hη : ∀ y, (η y).toNat ≤ K)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T t : ℕ) (ht : t ≤ T) (x : Site d) :
    (-η x).toNat ≤ (matchedState η ρ σ t).holes x + t * ((2 * T + 1) ^ d * K) := by
  induction t with
  | zero => simp [matchedState, initial]
  | succ t ih =>
      have hp := ih (by omega)
      have ha := matchedArrivals_le_box η K hη ρ σ t x
      have hpow : (2 * (t + 1) + 1) ^ d ≤ (2 * T + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      have hb := ha.trans (Nat.mul_le_mul_right K hpow)
      rw [matchedHoles_succ, Nat.succ_mul]
      omega

/-- A finite hole capacity large enough to act as a permanent sink until the given horizon. -/
def horizonSink (η : Site d → ℤ) (v : Site d) (T : ℕ) : Site d → ℤ :=
  Function.update η v (-((T * (2 * T + 1) ^ d + 1 : ℕ) : ℤ))

theorem horizonSink_particle_bound (η : Site d → ℤ) (v : Site d) (T : ℕ)
    (hη : ∀ y, (η y).toNat ≤ 1) : ∀ y, (horizonSink η v T y).toNat ≤ 1 := by
  classical
  intro y
  by_cases hy : y = v
  · subst y
    simp only [horizonSink, Function.update_self, Int.toNat_neg_natCast]
    omega
  · simpa only [horizonSink, Function.update_of_ne hy] using hη y

/-- This finite sink retains at least one hole throughout the prescribed horizon. -/
theorem horizonSink_holes_pos (η : Site d → ℤ) (v : Site d) (T : ℕ)
    (hη : ∀ y, (η y).toNat ≤ 1) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (t : ℕ) (ht : t ≤ T) : 0 < (matchedState (horizonSink η v T) ρ σ t).holes v := by
  have h := matchedHoles_loss_le (horizonSink η v T) 1 (horizonSink_particle_bound η v T hη)
    ρ σ T t ht v
  simp only [horizonSink, Function.update_self, neg_neg, Int.toNat_natCast, mul_one] at h
  have hm := Nat.mul_le_mul_right ((2 * T + 1) ^ d) ht
  dsimp only [horizonSink]
  omega

/-- No active particle or odometer departure occurs at the finite sink before its horizon. -/
theorem horizonSink_counts_zero (η : Site d → ℤ) (v : Site d) (T : ℕ)
    (hη : ∀ y, (η y).toNat ≤ 1) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (t : ℕ) (ht : t ≤ T) :
    matchedCount (horizonSink η v T) ρ σ t v = 0 ∧
      (matchedState (horizonSink η v T) ρ σ t).departures v = 0 := by
  have hc (s : ℕ) (hs : s ≤ T) : matchedCount (horizonSink η v T) ρ σ s v = 0 := by
    rcases matchedCount_eq_zero_or_holes_eq_zero (horizonSink η v T) ρ σ s v with h | h
    · exact h
    · exact False.elim ((Nat.ne_of_gt (horizonSink_holes_pos η v T hη ρ σ s hs)) h)
  refine ⟨hc t ht, ?_⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      change (matchedState (horizonSink η v T) ρ σ t).departures v +
        matchedCount (horizonSink η v T) ρ σ t v = 0
      rw [ih (by omega), hc t (by omega), zero_add]

/-- For the sparse initial fields, replacing the origin by the sink decreases the configuration. -/
theorem horizonSink_le (η : Site d → ℤ) (v : Site d) (T : ℕ) (hv : -1 ≤ η v) :
    ∀ y, horizonSink η v T y ≤ η y := by
  classical
  intro y
  by_cases hy : y = v
  · subst y
    simp only [horizonSink, Function.update_self]
    omega
  · simp only [horizonSink, Function.update_of_ne hy, le_refl]
end Parking
