import Parking.Support.NoArrivalFlag

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- A single initial hole survives exactly when there has been no entrance. -/
theorem matchedHole_eq_one_iff_noArrival (η : Site d → ℤ) (v : Site d) (hv : η v = -1)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) :
    (matchedState η ρ σ t).holes v = 1 ↔ noArrivalFlag η ρ σ t v = true := by
  induction t with
  | zero => simp [matchedState, initial, hv, noArrivalFlag]
  | succ t ih =>
      have hb := matchedHoles_le_initial η ρ σ t v
      rw [hv] at hb
      norm_num at hb
      rw [matchedHoles_succ, noArrivalFlag, Bool.and_eq_true, decide_eq_true_eq, ← ih]
      omega

/-- Before the first entrance, any two nonpositive capacities at the target give the same dynamics. -/
theorem noArrivalFlag_same_nonpositive_origin (η ζ : Site d → ℤ) (v : Site d)
    (hη : η v ≤ 0) (hζ : ζ v ≤ 0) (he : ∀ x, x ≠ v → η x = ζ x)
    (ρ ρ' : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) :
    noArrivalFlag η ρ σ T v = noArrivalFlag ζ ρ' σ T v := by
  classical
  have haux (t : ℕ) : noArrivalFlag η ρ σ t v = noArrivalFlag ζ ρ' σ t v ∧
      (noArrivalFlag η ρ σ t v = true →
        (∀ x, matchedCount η ρ σ t x = matchedCount ζ ρ' σ t x) ∧
        (∀ x, x ≠ v → (matchedState η ρ σ t).holes x = (matchedState ζ ρ' σ t).holes x)) := by
    induction t with
    | zero =>
        refine ⟨rfl, fun _ => ⟨fun x => ?_, fun x hx => ?_⟩⟩
        · rw [matchedCount_zero, matchedCount_zero]
          by_cases hx : x = v
          · subst x
            rw [Int.toNat_of_nonpos hη, Int.toNat_of_nonpos hζ]
          · rw [he x hx]
        · change (-η x).toNat = (-ζ x).toNat
          rw [he x hx]
    | succ t ih =>
        by_cases hf : noArrivalFlag η ρ σ t v = true
        · have hc := ih.2 hf
          have hcard (x : Site d) : (matchedArrivals η ρ σ t x).card = (matchedArrivals ζ ρ' σ t x).card := by
            rw [card_matchedArrivals_eq_countArrivals, card_matchedArrivals_eq_countArrivals,
              show matchedCount η ρ σ t = matchedCount ζ ρ' σ t from funext hc.1]
          refine ⟨by rw [noArrivalFlag, noArrivalFlag, ih.1, hcard], fun hnext => ?_⟩
          have hz : (matchedArrivals η ρ σ t v).card = 0 := by
            simpa only [noArrivalFlag, hf, Bool.true_and, decide_eq_true_eq] using hnext
          refine ⟨fun x => ?_, fun x hx => ?_⟩
          · rw [matchedCount_succ, matchedCount_succ]
            by_cases hx : x = v
            · subst x
              rw [← hcard, hz, Nat.zero_sub, Nat.zero_sub]
            · rw [hcard, hc.2 x hx]
          · rw [matchedHoles_succ, matchedHoles_succ, hcard, hc.2 x hx]
        · have hf' : noArrivalFlag η ρ σ t v = false := Bool.eq_false_iff.mpr hf
          have hg' : noArrivalFlag ζ ρ' σ t v = false := ih.1.symm.trans hf'
          simp [noArrivalFlag, hf', hg']
  exact (haux T).1
end Parking
