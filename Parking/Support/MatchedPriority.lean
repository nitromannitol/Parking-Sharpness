import Parking.Support.MatchedCounts

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Counts, holes and odometers in the common-table process do not depend on priorities. -/
theorem matchedState_counts_priority (η : Site d → ℤ)
    (ρ ρ' : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) :
    (∀ x, matchedCount η ρ σ t x = matchedCount η ρ' σ t x) ∧
    (∀ x, (matchedState η ρ σ t).holes x = (matchedState η ρ' σ t).holes x) ∧
    (∀ x, (matchedState η ρ σ t).departures x = (matchedState η ρ' σ t).departures x) := by
  induction t with
  | zero => simp [matchedCount_zero, matchedState]
  | succ t ih =>
      have ha (x : Site d) : (matchedArrivals η ρ σ t x).card = (matchedArrivals η ρ' σ t x).card := by
        rw [card_matchedArrivals, card_matchedArrivals]
        simp only [arrivalSlots, ih.1]
      refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
      · rw [matchedCount_succ, matchedCount_succ, ha, ih.2.1]
      · rw [matchedHoles_succ, matchedHoles_succ, ha, ih.2.1]
      · change (matchedState η ρ σ t).departures x + matchedCount η ρ σ t x =
          (matchedState η ρ' σ t).departures x + matchedCount η ρ' σ t x
        rw [ih.1, ih.2.2]

/-- The signed field at a restart time encodes exactly the remaining particles and holes. -/
def matchedRestart (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T : ℕ) (x : Site d) : ℤ :=
  matchedCount η ρ σ T x - (matchedState η ρ σ T).holes x

/-- Restarting the count process uses the future tables and discards only the old odometer. -/
theorem matchedState_restart (η : Site d → ℤ)
    (ρ ρ' : Label d × ℕ → ℝ) (σ : RoundNoise d) (T s : ℕ) :
    let ζ := matchedRestart η ρ σ T
    let τ : RoundNoise d := fun n => σ (T + n)
    (∀ x, matchedCount η ρ σ (T + s) x = matchedCount ζ ρ' τ s x) ∧
    (∀ x, (matchedState η ρ σ (T + s)).holes x = (matchedState ζ ρ' τ s).holes x) ∧
    (∀ x, (matchedState η ρ σ (T + s)).departures x =
      (matchedState η ρ σ T).departures x + (matchedState ζ ρ' τ s).departures x) := by
  dsimp only
  induction s with
  | zero =>
      simp only [Nat.add_zero, matchedCount_zero, matchedState]
      refine ⟨fun x => ?_, fun x => ?_, fun x => by simp [initial]⟩
      · have h := matchedCount_eq_zero_or_holes_eq_zero η ρ σ T x
        unfold matchedRestart
        omega
      · have h := matchedCount_eq_zero_or_holes_eq_zero η ρ σ T x
        change (matchedState η ρ σ T).holes x = (-(matchedRestart η ρ σ T x)).toNat
        unfold matchedRestart
        omega
  | succ s ih =>
      have ha (x : Site d) : (matchedArrivals η ρ σ (T + s) x).card =
          (matchedArrivals (matchedRestart η ρ σ T) ρ' (fun n => σ (T + n)) s x).card := by
        rw [card_matchedArrivals, card_matchedArrivals]
        simp only [arrivalSlots, ih.1]
      rw [show T + (s + 1) = T + s + 1 by omega]
      refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
      · rw [matchedCount_succ, matchedCount_succ, ha, ih.2.1]
      · rw [matchedHoles_succ, matchedHoles_succ, ha, ih.2.1]
      · change (matchedState η ρ σ (T + s)).departures x + matchedCount η ρ σ (T + s) x =
          (matchedState η ρ σ T).departures x +
            ((matchedState (matchedRestart η ρ σ T) ρ' (fun n => σ (T + n)) s).departures x +
              matchedCount (matchedRestart η ρ σ T) ρ' (fun n => σ (T + n)) s x)
        rw [ih.1, ih.2.2, Nat.add_assoc]
end Parking
