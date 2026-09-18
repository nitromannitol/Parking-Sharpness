import Parking.Support.SingleAddition
import Parking.Support.LabelGreen

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The unique discrepancy label accounts for the entire excess active count. -/
theorem singleAddition_count_difference (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    (matchedCount (addParticle v η) ρ σ t x : ℝ) - matchedCount η ρ σ t x =
      discrepancyDeparture (singleAdditionPair η v) ρ σ t (v, 0) x := by
  classical
  let c := singleAdditionPair η v
  let p : Label d := (v, 0)
  have hmem (q : Label d) : q ∈ discrepancyLeaving c ρ σ t x true ↔
      q = p ∧ discrepancyDoesMove c ρ σ t p = true ∧ (discrepancyState c ρ σ t).pos p = x := by
    simp only [discrepancyLeaving, discrepancyAtSign, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, _hs⟩, hm⟩
      have hq := (mem_discrepancyAt_iff c ρ σ t x q).mp ha
      have hqp : q = p := singleAddition_active_label η v ρ σ t q hq.1
      subst q
      exact ⟨rfl, by simpa only [discrepancyDoesMove, decide_eq_true_eq] using hm, hq.2⟩
    · rintro ⟨rfl, hm, hx⟩
      have hm' := of_decide_eq_true hm
      have ha : p ∈ discrepancyAt c (discrepancyState c ρ σ t) t x := by
        rw [← hx]
        exact hm'.1
      exact ⟨⟨ha, singleAddition_sign η v⟩, hm'⟩
  have hfin : discrepancyLeaving c ρ σ t x true =
      if discrepancyDoesMove c ρ σ t p = true ∧ (discrepancyState c ρ σ t).pos p = x
      then {p} else ∅ := by
    ext q
    rw [hmem]
    split <;> simp_all
  have hcard := card_discrepancyLeaving c ρ σ t (discrepancyBalance c ρ σ t) x true
  have he0 : coupledConf false c = η := rfl
  have he1 : coupledConf true c = addParticle v η := rfl
  simp only [Bool.not_true, he0, he1] at hcard
  rw [← Nat.cast_sub (singleAddition_counts_mono η v ρ σ t x).1, ← hcard, hfin]
  unfold discrepancyDeparture
  change ((if discrepancyDoesMove c ρ σ t p = true ∧ (discrepancyState c ρ σ t).pos p = x
    then ({p} : Finset (Label d)) else ∅).card : ℝ) = _
  split <;> simp_all [c, p]

/-- The cumulative odometer difference is exactly the departures carried by the unique label. -/
theorem singleAddition_odometer_difference (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    ((matchedState (addParticle v η) ρ σ T).departures x : ℝ) -
        ((matchedState η ρ σ T).departures x : ℝ) =
      ∑ t ∈ Finset.range T, discrepancyDeparture (singleAdditionPair η v) ρ σ t (v, 0) x := by
  induction T with
  | zero => simp [matchedState, initial]
  | succ T ih =>
      have hstep (η' : Site d → ℤ) : (matchedState η' ρ σ (T + 1)).departures x =
          (matchedState η' ρ σ T).departures x + matchedCount η' ρ σ T x := rfl
      rw [hstep, hstep, Finset.sum_range_succ]
      push_cast
      rw [← singleAddition_count_difference η v ρ σ T x, ← ih]
      ring

/-- Adding one initial particle changes the expected odometer by at most one Green function. -/
theorem integral_singleAddition_odometer_difference_le (hd : 3 ≤ d) (η : Site d → ℤ)
    (v : Site d) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    ∫ σ, (((matchedState (addParticle v η) ρ σ T).departures x : ℝ) -
        ((matchedState η ρ σ T).departures x : ℝ)) ∂(roundNoiseLaw d) ≤ fullGreen d (v - x) := by
  simp_rw [singleAddition_odometer_difference]
  exact integral_discrepancy_departures_le hd (singleAdditionPair η v) ρ (v, 0) x T
end Parking
