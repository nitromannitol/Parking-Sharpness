import Parking.Support.MatchedMeanBalance

/-!
# The no-arrival flag

`noArrivalFlag η ρ σ t x` records whether the target site `x` has received no matched
arrival in any of the first `t` completed rounds of the noise `σ`. This file gives the
recursive characterization `noArrivalFlag_iff`, its measurability in `σ`, and shows that
replacing a future noise layer at some index `n` leaves both the arrival counts before
round `n` and the no-arrival flag up to time `n` unchanged.
-/

open LatticeProb (measurable_from_countable')

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- No arrival at the target has occurred in the completed rounds. -/
def noArrivalFlag (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) : ℕ → Site d → Bool
  | 0, _ => true
  | t + 1, x => noArrivalFlag η ρ σ t x && decide ((matchedArrivals η ρ σ t x).card = 0)

/-- `noArrivalFlag η ρ σ t x` is true iff no round `s < t` had a matched arrival at `x`,
proved by induction on `t` unfolding the recursive definition. -/
theorem noArrivalFlag_iff (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ)
    (x : Site d) :
    noArrivalFlag η ρ σ t x = true ↔ ∀ s < t, (matchedArrivals η ρ σ s x).card = 0 := by
  induction t with
  | zero => simp [noArrivalFlag]
  | succ t ih =>
      simp only [noArrivalFlag, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨h, ht⟩ s hs
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact h s hs
        · exact ht
      · intro h
        exact ⟨fun s hs => h s (by omega), h t (by omega)⟩

/-- `fun σ => noArrivalFlag η ρ σ t x` is measurable in `σ`, by induction on `t` using the
measurability of the matched-arrival count `matchedArrivals`. -/
theorem measurable_noArrivalFlag (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (t : ℕ)
    (x : Site d) :
    Measurable (fun σ : RoundNoise d => noArrivalFlag η ρ σ t x) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hm : Measurable (fun σ : RoundNoise d => (matchedArrivals η ρ σ t x).card) := by
        simp_rw [card_matchedArrivals_eq_countArrivals]
        exact (measurable_from_countable' Finset.card).comp
          (measurable_countArrivals _ _ (measurable_matchedCount ⟨0, hd⟩ (fun _ => η)
              (fun _ => ρ) id
            measurable_const measurable_const measurable_id t) (measurable_pi_apply t) x)
      exact (measurable_from_countable' (fun q : Bool × ℕ => q.1 && decide (q.2 = 0))).comp
          (ih.prodMk hm)

/-- Replacing a future layer leaves the earlier arrival counts unchanged. -/
theorem card_matchedArrivals_update (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (n t : ℕ) (τ : RoundSlot d → Fin d × Bool) (ht : t < n) (x : Site d) :
    (matchedArrivals η ρ (Function.update σ n τ) t x).card = (matchedArrivals η ρ σ t x).card := by
  have he : matchedCount η ρ (Function.update σ n τ) t = matchedCount η ρ σ t := by
    funext y
    unfold matchedCount
    rw [matchedState_update η ρ σ n t τ ht.le]
  rw [card_matchedArrivals_eq_countArrivals, card_matchedArrivals_eq_countArrivals, he,
    Function.update_of_ne (Nat.ne_of_lt ht)]

/-- The no-arrival history is fixed before the next layer is read. -/
theorem noArrivalFlag_update (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (n t : ℕ) (τ : RoundSlot d → Fin d × Bool) (ht : t ≤ n) (x : Site d) :
    noArrivalFlag η ρ (Function.update σ n τ) t x = noArrivalFlag η ρ σ t x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [noArrivalFlag, noArrivalFlag, ih (by omega),
        card_matchedArrivals_update η ρ σ n t τ (by omega)]
end Parking
