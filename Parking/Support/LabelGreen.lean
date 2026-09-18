/-
The expected departures of a discrepancy label are bounded by the walk Green function.
-/
import Parking.Support.GreenPotential
import Parking.Support.LayerReward
import Parking.Support.DiscrepancyFresh

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A unit reward for a departure from x carried by one persistent discrepancy label. -/
def discrepancyDeparture (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (p : Label d) (x : Site d) : ℝ :=
  if discrepancyDoesMove c ρ σ t p = true ∧ (discrepancyState c ρ σ t).pos p = x then 1 else 0

/-- One-label motion is a fresh step or a wait, with the choice fixed by the past. -/
theorem discrepancyPosition_update_succ (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (p : Label d) (τ : RoundSlot d → Fin d × Bool) :
    (discrepancyState c ρ (Function.update σ t τ) (t + 1)).pos p =
      if discrepancyDoesMove c ρ σ t p then
        (discrepancyState c ρ σ t).pos p + stepVec (τ (discrepancyIndex c ρ σ t p))
      else (discrepancyState c ρ σ t).pos p := by
  classical
  change discrepancyNextPos c ρ _ _ _ _ t p = _
  rw [matchedCount_update _ ρ σ t t τ le_rfl, matchedCount_update _ ρ σ t t τ le_rfl,
    discrepancyState_update c ρ σ t t τ le_rfl, Function.update_self]
  simp only [discrepancyNextPos, discrepancyDoesMove, discrepancyIndex, decide_eq_true_eq]

/-- The Green potential pays exactly for a departure carried by a fixed discrepancy label. -/
theorem integral_discrepancy_green_step (hd : 3 ≤ d) (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (p : Label d) (x : Site d) :
    ∫ τ, fullGreen d ((discrepancyState c ρ (Function.update σ t τ) (t + 1)).pos p - x)
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) =
        fullGreen d ((discrepancyState c ρ σ t).pos p - x) - discrepancyDeparture c ρ σ t p x := by
  haveI := stepLaw_isProbability (by omega : 1 ≤ d)
  simp only [discrepancyPosition_update_succ]
  by_cases h : discrepancyDoesMove c ρ σ t p = true
  · simp only [h, ↓reduceIte, discrepancyDeparture, true_and]
    exact integral_table_green hd _ x _
  · have h' : discrepancyDoesMove c ρ σ t p = false := Bool.eq_false_iff.mpr h
    simp [h', discrepancyDeparture]

/-- The expected number of departures carried by one label is bounded by the walk Green function. -/
theorem integral_discrepancy_departures_le (hd : 3 ≤ d) (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (p : Label d) (x : Site d) (T : ℕ) :
    ∫ σ, ∑ t ∈ Finset.range T, discrepancyDeparture c ρ σ t p x ∂(roundNoiseLaw d) ≤
      fullGreen d (p.1 - x) := by
  classical
  haveI := stepLaw_isProbability (by omega : 1 ≤ d)
  let V : RoundNoise d → ℕ → ℝ := fun σ t => fullGreen d ((discrepancyState c ρ σ t).pos p - x)
  let r : RoundNoise d → ℕ → ℝ := fun σ t => discrepancyDeparture c ρ σ t p x
  have hS (t : ℕ) := measurableState_discrepancyState (d := d) ⟨0, by omega⟩
    (Ω := RoundNoise d) (fun _ => c) (fun _ => ρ) id
    measurable_const measurable_const measurable_id t
  have hV (t : ℕ) : Measurable fun σ => V σ t :=
    (measurable_from_countable' (fullGreen d)).comp ((hS t).2.1 p |>.sub measurable_const)
  have hr (t : ℕ) : Measurable fun σ => r σ t := by
    have ha := measurable_matchedCount (d := d) ⟨0, by omega⟩ (Ω := RoundNoise d)
      (fun _ => coupledConf false c) (fun _ => ρ) id
      measurable_const measurable_const measurable_id t
    have hb := measurable_matchedCount (d := d) ⟨0, by omega⟩ (Ω := RoundNoise d)
      (fun _ => coupledConf true c) (fun _ => ρ) id
      measurable_const measurable_const measurable_id t
    have hm := measurable_discrepancyMoving (Ω := RoundNoise d)
      (fun _ => c) (fun _ => ρ) _ _ _ measurable_const measurable_const ha hb (hS t) t p
    have hm' : MeasurableSet {σ | discrepancyDoesMove c ρ σ t p = true} := by
      simpa only [discrepancyDoesMove, decide_eq_true_eq, id_eq] using measurableSet_setOf.mpr hm
    exact Measurable.ite (hm'.inter (measurableSet_eq_fun ((hS t).2.1 p) measurable_const))
      measurable_const measurable_const
  apply layer_reward_sum_le (Measure.infinitePi fun _ : RoundSlot d => stepLaw d)
    V r hV hr (escapeConst d) _ _ _ (fullGreen d (p.1 - x)) _ T
  · intro σ t
    exact ⟨fullGreen_nonneg d _, fullGreen_le_escapeConst hd _⟩
  · intro σ t
    change 0 ≤ discrepancyDeparture c ρ σ t p x ∧ discrepancyDeparture c ρ σ t p x ≤ 1
    unfold discrepancyDeparture
    split <;> norm_num
  · intro σ t
    exact (integral_discrepancy_green_step hd c ρ σ t p x).le
  · intro σ
    rfl
end Parking
