import Parking.Frozen.CorCritical

noncomputable section
namespace Parking
open MeasureTheory Filter
variable {d : ℕ}

/-- The critical density lower bound forces the mean odometer to diverge. -/
theorem meanU_tendsto_atTop (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hi : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hm : ∫ k, (k : ℝ) ∂ν = 0) :
    Tendsto (meanU (law d ν)) atTop atTop := by
  obtain ⟨c, hc, hall⟩ := Parking.Frozen.cor_critical
  obtain ⟨C, _, hb⟩ := hall d hd ν inferInstance hnc hi hm
  apply tendsto_atTop.mpr
  intro B
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop ((B + C) / c))
  filter_upwards [hlog, eventually_ge_atTop 2] with n hn hn2
  change (B + C) / c ≤ Real.log (n : ℝ) at hn
  have hn' := (div_le_iff₀ hc).mp hn
  have hb' := (le_max_right (meanu (law d ν) n) (c * Real.log n - C)).trans (hb n hn2)
  linarith
end Parking
