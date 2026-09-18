/-
The divisible mean is smaller than log n and the mean ratio diverges in high dimensions.
-/
import Parking.Support.MeanPos
import Parking.Support.GrowthMeans

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped Topology
variable {d : ℕ}

theorem realLaw_bounded_below (ν : Measure ℤ) (hb : ∃ b : ℤ, ν (Set.Iio b) = 0) :
    ∃ b : ℝ, ∀ᵐ z ∂(realLaw ν), b ≤ z := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨(b : ℝ), ?_⟩
  rw [realLaw]
  apply (ae_map_iff measurable_intCastReal.aemeasurable
    (show MeasurableSet {z : ℝ | (b : ℝ) ≤ z} from
      measurableSet_le measurable_const measurable_id)).mpr
  have h : ∀ᵐ k ∂ν, b ≤ k := by
    rw [ae_iff]
    simp only [not_le]
    exact hb
  filter_upwards [h] with k hk
  exact_mod_cast hk

/-- With a lower bound on the initial field, the high-dimensional divisible mean is o(log n). -/
theorem high_meanu_div_log_tendsto_zero (hd : 1 ≤ d) (hd5 : 5 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hb : ∃ b : ℤ, ν (Set.Iio b) = 0) :
    Tendsto (fun n : ℕ => meanu (law d ν) n / Real.log n) atTop (𝓝 0) := by
  haveI := hν.prob
  have hBP := hGrowth d hd (realLaw ν) inferInstance (realLaw_mean ν hν)
    (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν) (realLaw_expMoment ν hν)
  obtain ⟨c, C, _hc, hC, hu⟩ := hBP.2.2.2.1 hd5 (realLaw_bounded_below ν hb)
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd5
  have hγ : (2 : ℝ) / d < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hpow := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - (2 : ℝ) / d)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim : Tendsto (fun n : ℕ => C * (Real.log n) ^ (- (1 - (2 : ℝ) / d)))
      atTop (𝓝 0) := by simpa only [Function.comp_def, mul_zero] using hpow.const_mul C
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (meanu_pos hd ν hν n (by omega)).le
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hup := (hu n hn).2
    rw [← meanu_eq_meanSandpileReal hd ν n] at hup
    calc
      meanu (law d ν) n / Real.log n ≤ C * (Real.log n) ^ ((2 : ℝ) / d) / Real.log n :=
        div_le_div_of_nonneg_right hup hlog.le
      _ = C * (Real.log n) ^ (- (1 - (2 : ℝ) / d)) := by
        rw [neg_sub, Real.rpow_sub hlog, Real.rpow_one]
        ring

/-- The high-dimensional ratio diverges when the field is bounded below. -/
theorem high_mean_ratio_tendsto_atTop (hd : 1 ≤ d) (hd5 : 5 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) (hb : ∃ b : ℤ, ν (Set.Iio b) = 0) :
    Tendsto (fun n : ℕ => meanU (law d ν) n / meanu (law d ν) n) atTop atTop := by
  obtain ⟨c, C, hc, _hC, hU⟩ := (meanU_growth hGrowth hBern hConc hGN d hd ν hν).2 (by omega)
  have hlim := high_meanu_div_log_tendsto_zero hd hd5 hGrowth ν hν hb
  apply tendsto_atTop.mpr
  intro B
  let M : ℝ := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he := hlim.eventually (gt_mem_nhds (by positivity : 0 < c / M))
  filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hmu := meanu_pos hd ν hν n (by omega)
  apply (le_div_iff₀ hmu).mpr
  have h1 : M * meanu (law d ν) n ≤ c * Real.log n := by
    rw [div_lt_iff₀ hlog] at hn
    have h2 := mul_le_mul_of_nonneg_left hn.le hM.le
    field_simp at h2
    nlinarith only [h2]
  calc
    B * meanu (law d ν) n ≤ M * meanu (law d ν) n :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hmu.le
    _ ≤ c * Real.log n := h1
    _ ≤ meanU (law d ν) n := (hU n hn2).1
end Parking
