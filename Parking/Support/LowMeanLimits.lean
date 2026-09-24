/-
The low-dimensional mean ratio and odometer scaling limit.
-/
import Parking.Support.DiscrepancyLimits
import Parking.Support.MeanPos

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped Topology

/-- The low-dimensional ratio of the two mean odometers tends to one. -/
theorem low_mean_ratio_tendsto_one {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    Tendsto (fun n : ℕ => meanU (law d ν) n / meanu (law d ν) n) atTop (𝓝 1) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  have hL := (discrepancy_moment_tendsto_zero hd hd3 hGrowth hBern hConc hGN ν hν 1
    (by norm_num)).2
  simp only [Real.rpow_one] at hL
  have hdiff : Tendsto (fun n : ℕ => ∫ ω, ((U ω n 0 : ℝ) - uOf ω n 0) /
      meanu (law d ν) n ∂(law d ν)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) ?_ hL
    intro n
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := law d ν)
      (fun ω : Data d => ((U ω n 0 : ℝ) - uOf ω n 0) / meanu (law d ν) n))
  have hsum : Tendsto (fun n : ℕ =>
      (∫ ω, ((U ω n 0 : ℝ) - uOf ω n 0) / meanu (law d ν) n ∂(law d ν)) + 1)
      atTop (𝓝 1) := by simpa only [zero_add] using hdiff.add_const 1
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [integral_div, integral_sub (integrable_U_law hd ν hν.integrable_abs n 0)
    (integrable_uOf hd ν hν.integrable_abs n 0)]
  change (meanU (law d ν) n - meanu (law d ν) n) / meanu (law d ν) n + 1 =
    meanU (law d ν) n / meanu (law d ν) n
  field_simp [(meanu_pos hd ν hν n hn).ne']
  ring

/-- The mean particle odometer has the same positive scaling limit as the sandpile. -/
theorem low_meanU_scaling_limit {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ =>
      (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * meanU (law d ν) n) atTop (𝓝 L) := by
  haveI := hν.prob
  have hBP := hGrowth d hd (realLaw ν) inferInstance (realLaw_mean ν hν)
    (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν) (realLaw_expMoment ν hν)
  obtain ⟨L, hL, hsp⟩ := hBP.2.2.2.2 hd3
  have hsp' : Tendsto (fun n : ℕ =>
      (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * meanu (law d ν) n) atTop (𝓝 L) := by
    simpa only [meanu_eq_meanSandpileReal hd ν] using hsp
  have hratio := low_mean_ratio_tendsto_one hd hd3 hGrowth hBern hConc hGN ν hν
  have hprod : Tendsto (fun n : ℕ =>
      ((n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * meanu (law d ν) n) *
        (meanU (law d ν) n / meanu (law d ν) n)) atTop (𝓝 L) := by
    simpa only [mul_one] using hsp'.mul hratio
  refine ⟨L, hL, hprod.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  field_simp [(meanu_pos hd ν hν n hn).ne']
end Parking
