/- Step 3 of the oriented walk theorem, the half that needs no scaling
proposition: the ratio of the directed particle mean to the directed divisible
mean tends to one (`parking.tex:3296-3312`). -/
import Parking.Support.OrientedMeanBound
import Parking.Support.OrientedMeanComparison
import Mathlib

noncomputable section
namespace Parking
open MeasureTheory Filter Topology
variable {d : ℕ}

/-- A power of a logarithm divided by a positive power of `n` tends to zero. -/
theorem tendsto_log_rpow_div_rpow (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) ^ b / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => Real.log x ^ b / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop b ha).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => Real.log (x + 1) ^ b / x ^ a) atTop (𝓝 0) := by
    have hb2 : Tendsto (fun x : ℝ => 2 ^ b * (Real.log x ^ b / x ^ a)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hbase.const_mul (2 ^ b)
    refine squeeze_zero' ?_ ?_ hb2
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) b) (Real.rpow_nonneg hx.le a)
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
      have hlogx0 : 0 ≤ Real.log x := le_trans (Real.log_nonneg (by norm_num)) hlogx
      have hle : Real.log (x + 1) ≤ 2 * Real.log x := by
        have h2 : Real.log (x + 1) ≤ Real.log (2 * x) :=
          Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h2
        linarith
      have hlog1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
      calc Real.log (x + 1) ^ b / x ^ a
          ≤ (2 * Real.log x) ^ b / x ^ a := by
            apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hx0.le a)
            exact Real.rpow_le_rpow hlog1 hle hb.le
        _ = 2 ^ b * (Real.log x ^ b / x ^ a) := by
            rw [Real.mul_rpow (by norm_num) hlogx0]
            ring
  exact h1.comp tendsto_natCast_atTop_atTop

/-- Step 3 of `thm:oriented-walk` (`parking.tex:3296-3312`), the half that needs
no scaling proposition: `eq:oriented-particle-error` together with the lower
`n^{1/4}` bound on the divisible mean gives `E U⃗_n(0)/E u⃗_n(0) → 1`. -/
theorem tendsto_meanU_div_meanuOriented (ν : Measure ℤ) (hν : CriticalLaw ν) (c C : ℝ)
    (hc : 0 < c)
    (hlo : ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanuOriented (orientedLaw 2 ν) n)
    (herr : ∀ n : ℕ, 1 ≤ n →
      |meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n| ≤
        C * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)) :
    Tendsto (fun n : ℕ => meanU (orientedLaw 2 ν) n / meanuOriented (orientedLaw 2 ν) n)
      atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ =>
      (meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n) /
        meanuOriented (orientedLaw 2 ν) n) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ =>
        (C / c) * (Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) / (n : ℝ) ^ ((1 : ℝ) / 8)))
        atTop (𝓝 0) := by
      simpa using (tendsto_log_rpow_div_rpow (1 / 8) (3 / 4) (by norm_num) (by norm_num)).const_mul (C / c)
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hdpos : 0 < meanuOriented (orientedLaw 2 ν) n := by
        have hpos : 0 < c * (n : ℝ) ^ ((1 : ℝ) / 4) := by
          have : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
          positivity
        exact lt_of_lt_of_le hpos (hlo n hn)
      exact div_nonneg (sub_nonneg.mpr (meanuOriented_le_meanU (by norm_num) ν hν n)) hdpos.le
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hden : c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanuOriented (orientedLaw 2 ν) n := hlo n hn
      have hpos : 0 < c * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
        positivity
      have hdpos : 0 < meanuOriented (orientedLaw 2 ν) n := lt_of_lt_of_le hpos hden
      calc (meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n) /
            meanuOriented (orientedLaw 2 ν) n
          ≤ (C * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)) /
            (c * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
            div_le_div₀ (le_trans (abs_nonneg _) (herr n hn))
              (le_trans (le_abs_self _) (herr n hn)) hpos hden
        _ = (C / c) * (Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) / (n : ℝ) ^ ((1 : ℝ) / 8)) := by
            have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
            have h14 : (n : ℝ) ^ ((1 : ℝ) / 4) =
                (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 8) := by
              rw [← Real.rpow_add hn0]; norm_num
            rw [h14]
            field_simp
  have h2 : Tendsto (fun n : ℕ => 1 + (meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n) /
      meanuOriented (orientedLaw 2 ν) n) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hlim
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hdpos : 0 < meanuOriented (orientedLaw 2 ν) n := by
    have hpos : 0 < c * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
      positivity
    exact lt_of_lt_of_le hpos (hlo n hn)
  field_simp
  ring

end Parking
end
