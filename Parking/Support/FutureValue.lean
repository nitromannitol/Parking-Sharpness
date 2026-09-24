import Parking.Support.MatchedBellman

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Restarting from the signed field recovers exactly the active and hole counts. -/
theorem matchedRestart_parts (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (s : ℕ) (y : Site d) :
    (matchedRestart η ρ σ s y).toNat = matchedCount η ρ σ s y ∧
      (-(matchedRestart η ρ σ s y)).toNat = (matchedState η ρ σ s).holes y := by
  have h := matchedCount_eq_zero_or_holes_eq_zero η ρ σ s y
  unfold matchedRestart
  omega

theorem matchedRestart_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) :
    matchedRestart η ρ σ 0 = η := by
  funext x
  simp only [matchedRestart, matchedCount_zero, matchedState, initial]
  omega

theorem matchedRestart_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (s : ℕ) :
    matchedRestart η ρ σ (s + 1) =
      roundSigned (matchedCount η ρ σ s) (matchedState η ρ σ s).holes (σ s) := by
  funext x
  have h := matchedSigned_succ η ρ σ s x
  change matchedRestart η ρ σ (s + 1) x = _ at h
  rw [h, card_matchedArrivals]
  rfl

/-- Past departures plus the expected future odometer. -/
def futureValue (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T s : ℕ) (x : Site d) : ℝ :=
  ((matchedState η ρ σ s).departures x : ℝ) + matchedMeanU (matchedRestart η ρ σ s) ρ (T - s) x

theorem futureValue_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T : ℕ) (x : Site d) : futureValue η ρ σ T 0 x = matchedMeanU η ρ T x := by
  simp [futureValue, matchedRestart_zero, matchedState, initial]

theorem futureValue_terminal (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T : ℕ) (x : Site d) : futureValue η ρ σ T T x = ((matchedState η ρ σ T).departures x : ℝ) := by
  simp [futureValue, matchedMeanU, matchedState, initial]

/-- The value after a round is the previous departures plus the future mean for its realized table. -/
theorem futureValue_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T s : ℕ) (x : Site d) :
    futureValue η ρ σ T (s + 1) x =
      ((matchedState η ρ σ s).departures x : ℝ) + (matchedCount η ρ σ s x : ℝ) +
      matchedMeanU (roundSigned (matchedCount η ρ σ s) (matchedState η ρ σ s).holes (σ s))
        ρ (T - s - 1) x := by
  unfold futureValue
  rw [matchedRestart_succ, show T - (s + 1) = T - s - 1 by omega]
  change (((matchedState η ρ σ s).departures x + matchedCount η ρ σ s x : ℕ) : ℝ) + _ = _
  rw [Nat.cast_add]

/-- Before a round is revealed, its table is averaged in the future value. -/
theorem futureValue_bellman (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T s : ℕ) (hs : s < T) (x : Site d) :
    futureValue η ρ σ T s x =
      ((matchedState η ρ σ s).departures x : ℝ) + (matchedCount η ρ σ s x : ℝ) +
      ∫ τ, matchedMeanU (roundSigned (matchedCount η ρ σ s) (matchedState η ρ σ s).holes τ)
        ρ (T - s - 1) x ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
  unfold futureValue
  rw [show T - s = (T - s - 1) + 1 by omega, matchedMeanU_bellman hd]
  have hA : (fun y => (matchedRestart η ρ σ s y).toNat) = matchedCount η ρ σ s :=
    funext fun y => (matchedRestart_parts η ρ σ s y).1
  have hH : (fun y => (-(matchedRestart η ρ σ s y)).toNat) = (matchedState η ρ σ s).holes :=
    funext fun y => (matchedRestart_parts η ρ σ s y).2
  rw [hA, hH, (matchedRestart_parts η ρ σ s x).1]
  simp only [Nat.add_sub_cancel]
  ring
end Parking
