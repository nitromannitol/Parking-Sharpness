import Parking.Support.MatchedPriority
import Parking.Support.MeanLaw
import Parking.Support.InstructionField
import LatticeProb.Prob.InfinitePiSplit

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The signed field after the first round depends only on that round's table. -/
theorem matchedRestart_one (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (τ : RoundSlot d → Fin d × Bool) (σ : RoundNoise d) :
    matchedRestart η ρ (consNat τ σ) 1 =
      roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ := by
  funext x
  have h := matchedSigned_succ η ρ (consNat τ σ) 0 x
  change matchedRestart η ρ (consNat τ σ) 1 x = _ at h
  rw [h, card_matchedArrivals]
  simp only [roundSigned, arrivalSlots, countArrivals, matchedCount_zero, consNat_zero,
    matchedState, initial]

/-- The odometer satisfies the pathwise first-round decomposition. -/
theorem matchedOdometer_cons (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (τ : RoundSlot d → Fin d × Bool) (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    (matchedState η ρ (consNat τ σ) (T + 1)).departures x = (η x).toNat +
      (matchedState (roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ) ρ σ T).departures x := by
  have h := (matchedState_restart η ρ ρ (consNat τ σ) 1 T).2.2 x
  rw [Nat.add_comm 1 T, matchedRestart_one] at h
  have he : (fun n => consNat τ σ (1 + n)) = σ := by
    funext n
    rw [Nat.add_comm, consNat_succ]
  rw [he] at h
  have h1 : (matchedState η ρ (consNat τ σ) 1).departures x = (η x).toNat := by
    change 0 + matchedCount η ρ (consNat τ σ) 0 x = _
    rw [zero_add, matchedCount_zero]
  rw [h1] at h
  exact h

/-- Expected odometers are nonnegative. -/
theorem matchedMeanU_nonneg (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) : 0 ≤ matchedMeanU η ρ T x :=
  integral_nonneg fun _ => Nat.cast_nonneg _

/-- The same deterministic candidate bound holds for the mean odometer. -/
theorem matchedMeanU_le_candidates (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    matchedMeanU η ρ T x ≤ ((T * (candidates η x T).card : ℕ) : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  have h := integral_mono (integrable_matchedOdometer hd η ρ T x)
    (integrable_const ((T * (candidates η x T).card : ℕ) : ℝ))
    (fun σ => Nat.cast_le.mpr (matchedOdometer_le_candidates η ρ σ T x))
  simpa only [matchedMeanU, integral_const, probReal_univ, one_smul] using h

/-- The expected first-round decomposition, with every initial field allowed. -/
theorem matchedMeanU_bellman (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    matchedMeanU η ρ (T + 1) x = ((η x).toNat : ℝ) +
      ∫ τ, matchedMeanU (roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ) ρ T x
        ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI := roundNoiseLaw_isProbability hd
  let Q := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  let f : RoundNoise d → ℝ := fun σ => ((matchedState η ρ σ (T + 1)).departures x : ℝ)
  have hfi : Integrable f (roundNoiseLaw d) := integrable_matchedOdometer hd η ρ (T + 1) x
  have hprod : Integrable (fun q : (RoundSlot d → Fin d × Bool) × RoundNoise d => f (consNat q.1 q.2))
      (Q.prod (roundNoiseLaw d)) :=
    (show MeasurePreserving (fun q => consNat q.1 q.2) (Q.prod (roundNoiseLaw d)) (roundNoiseLaw d)
      from ⟨measurable_consNat, map_consNat Q⟩).integrable_comp_of_integrable hfi
  have hinner (τ : RoundSlot d → Fin d × Bool) : ∫ σ, f (consNat τ σ) ∂(roundNoiseLaw d) =
      ((η x).toNat : ℝ) + matchedMeanU (roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ) ρ T x := by
    simp only [f, matchedOdometer_cons, Nat.cast_add]
    rw [integral_add (integrable_const _) (integrable_matchedOdometer hd _ _ _ _)]
    simp only [integral_const, probReal_univ, one_smul, matchedMeanU]
  have hi : Integrable (fun τ => ((η x).toNat : ℝ) +
      matchedMeanU (roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ) ρ T x) Q := by
    have he := funext hinner
    exact he ▸ hprod.integral_prod_left
  change (∫ σ, f σ ∂(roundNoiseLaw d)) = _
  rw [show (∫ σ, f σ ∂(roundNoiseLaw d)) =
    ∫ τ, ∫ σ, f (consNat τ σ) ∂(roundNoiseLaw d) ∂Q from
      integral_infinitePi_nat_head_tail Q f hfi]
  simp_rw [hinner]
  have hj := integrable_const_add_iff.mp hi
  rw [integral_add (integrable_const _) hj]
  simp [Q]
end Parking
