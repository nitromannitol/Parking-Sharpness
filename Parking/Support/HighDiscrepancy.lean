/-
Logarithmic bounds for the high-dimensional absolute discrepancy.
-/
import Parking.Support.AbsoluteMeanPos
import Parking.Support.HighMeanLimits
import Parking.Support.BoundExtension

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped Topology
variable {d : ℕ}

/-- The absolute discrepancy lies between the difference and the sum of the mean odometers. -/
theorem integral_abs_discrepancy_bounds (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) :
    meanU (law d ν) n - meanu (law d ν) n ≤
        ∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν) ∧
      (∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν)) ≤
        meanU (law d ν) n + meanu (law d ν) n := by
  have hU := integrable_U_law hd ν hi n 0
  have hu := integrable_uOf hd ν hi n 0
  constructor
  · rw [meanU, meanu, ← integral_sub hU hu]
    exact integral_mono (hU.sub hu) (hU.sub hu).abs (fun _ => le_abs_self _)
  · rw [meanU, meanu, ← integral_add hU hu]
    apply integral_mono (hU.sub hu).abs (hU.add hu)
    intro ω
    calc
      |(U ω n 0 : ℝ) - uOf ω n 0| ≤ |(U ω n 0 : ℝ)| + |uOf ω n 0| := abs_sub _ _
      _ = (U ω n 0 : ℝ) + uOf ω n 0 := by
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (show 0 ≤ uOf ω n 0 from u_real_nonneg _ _ _)]

/-- In high dimensions both the particle mean and its absolute discrepancy grow like log n. -/
theorem high_mean_discrepancy_bounds (hd : 1 ≤ d) (hd5 : 5 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) (hb : ∃ b : ℤ, ν (Set.Iio b) = 0) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (law d ν) n ∧ meanU (law d ν) n ≤ C * Real.log n ∧
      c * Real.log n ≤ ∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν) ∧
      (∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν)) ≤ C * Real.log n := by
  haveI := hν.prob
  obtain ⟨c, C, hc, hC, hU⟩ := (meanU_growth hGrowth hBern hConc hGN d hd ν hν).2 (by omega)
  let f : ℕ → ℝ := fun n => ∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν)
  have hlog (n : ℕ) (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have he := (high_meanu_div_log_tendsto_zero hd hd5 hGrowth ν hν hb).eventually
    (gt_mem_nhds (by positivity : 0 < c / 2))
  have hlo : ∀ᶠ (n : ℕ) in atTop, c / 2 * Real.log n ≤ f n := by
    filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
    have h := (div_lt_iff₀ (hlog n hn2)).mp hn
    have hl := (hU n hn2).1
    have hf := (integral_abs_discrepancy_bounds hd ν hν.integrable_abs n).1
    change meanU (law d ν) n - meanu (law d ν) n ≤ f n at hf
    linarith only [h, hl, hf]
  obtain ⟨a, ha, _hac, hfa⟩ := extend_positive_lower_bound f (fun n => Real.log n) 2
    (integral_abs_discrepancy_pos hd ν hν) hlog (by positivity : 0 < c / 2) hlo
  refine ⟨min c a, max (min c a) (2 * C), lt_min hc ha, le_max_left _ _, fun n hn => ?_⟩
  have hlog0 := (hlog n hn).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hlog0).trans (hU n hn).1
  · apply (hU n hn).2.trans
    apply mul_le_mul_of_nonneg_right _ hlog0
    exact (by linarith : C ≤ 2 * C).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0).trans (hfa n hn)
  · have hf := (integral_abs_discrepancy_bounds hd ν hν.integrable_abs n).2
    have hu := meanu_le_meanU hd ν hν.integrable_abs n
    calc
      (∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν)) ≤ 2 * meanU (law d ν) n := by linarith
      _ ≤ 2 * (C * Real.log n) := mul_le_mul_of_nonneg_left (hU n hn).2 (by norm_num)
      _ = (2 * C) * Real.log n := by ring
      _ ≤ max (min c a) (2 * C) * Real.log n := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog0
end Parking
