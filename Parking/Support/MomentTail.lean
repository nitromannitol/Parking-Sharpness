/-
Real moment norms, logarithm domination and logarithmic-exponent tail bounds.
-/
import Parking.Support.UpperTarget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace Parking
open MeasureTheory Filter

/-- Markov's inequality in terms of the real r-th moment norm. -/
theorem measure_gt_le_rNorm_div_rpow {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hint : Integrable (fun ω => |f ω| ^ r) μ) :
    (μ {ω | a < |f ω|}).toReal ≤ (rNorm μ r f / a) ^ r := by
  have hI0 : 0 ≤ ∫ ω, |f ω| ^ r ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
  have haR : 0 < a ^ r := Real.rpow_pos_of_pos ha r
  have hM := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => Real.rpow_nonneg (abs_nonneg (f ω)) r) hint (a ^ r)
  have hsub : (μ {ω | a < |f ω|}).toReal ≤ (μ {ω | a ^ r ≤ |f ω| ^ r}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun ω hω => Real.rpow_le_rpow ha.le hω.le hr.le)
  have hbound : (μ {ω | a < |f ω|}).toReal ≤ (∫ ω, |f ω| ^ r ∂μ) / a ^ r := by
    apply (le_div_iff₀ haR).mpr
    have hm := mul_le_mul_of_nonneg_left hsub haR.le
    change a ^ r * (μ {ω | a ^ r ≤ |f ω| ^ r}).toReal ≤ _ at hM
    nlinarith
  refine hbound.trans_eq ?_
  rw [Real.div_rpow (rNorm_nonneg μ r f) ha.le, rNorm,
    ← Real.rpow_mul hI0, one_div_mul_cancel (ne_of_gt hr), Real.rpow_one]

/-- Any power of the logarithm is eventually dominated by a positive power. -/
theorem eventually_log_succ_rpow_le {a b δ γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hγ : 0 ≤ γ) :
    ∀ᶠ n : ℕ in atTop, a * Real.log ((n : ℝ) + 1) ^ γ ≤ b * (n : ℝ) ^ δ := by
  let K := a * 2 ^ γ / b
  have hK : 0 < K := by dsimp [K]; positivity
  have hs := ((isLittleO_log_rpow_rpow_atTop γ hδ).const_mul_left K).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := hs.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop 2, he] with n hn hnB
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : 0 ≤ Real.log n := (log_pos_of_two_le hn).le
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  change ‖K * Real.log (n : ℝ) ^ γ‖ ≤ 1 * ‖(n : ℝ) ^ δ‖ at hnB
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul] at hnB
  have hpow : Real.log ((n : ℝ) + 1) ^ γ ≤ 2 ^ γ * Real.log n ^ γ := by
    rw [← Real.mul_rpow (by norm_num) hlog0]
    exact Real.rpow_le_rpow hL0 (log_succ_le_two_mul_log hn) hγ
  have h1 := mul_le_mul_of_nonneg_left hpow ha.le
  have h2 := mul_le_mul_of_nonneg_left hnB hb.le
  dsimp [K] at h2
  have heq : b * (a * 2 ^ γ / b * Real.log (n : ℝ) ^ γ) =
      a * (2 ^ γ * Real.log n ^ γ) := by field_simp
  rw [heq] at h2
  exact h1.trans h2
end Parking

namespace Parking
open MeasureTheory Filter

/-- A power saving at a logarithmic moment exponent gives a Gaussian bound in log n. -/
theorem eventually_measure_gt_le_exp_log_sq {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (r a : ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hr : ∀ n, 0 < r n)
    (hint : ∀ n, Integrable (fun ω => |f n ω| ^ r n) μ)
    (hb : ∀ᶠ n : ℕ in atTop, rNorm μ (r n) (f n) / a n ≤ (n : ℝ) ^ (-δ) ∧
      0 < a n ∧ Real.log n ≤ r n) :
    ∀ᶠ n : ℕ in atTop, (μ {ω | a n < |f n ω|}).toReal ≤
      Real.exp (-(δ * Real.log n ^ 2)) := by
  filter_upwards [eventually_ge_atTop 2, hb] with n hn hB
  obtain ⟨hN, ha, hlogr⟩ := hB
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  calc (μ {ω | a n < |f n ω|}).toReal ≤ (rNorm μ (r n) (f n) / a n) ^ r n :=
        measure_gt_le_rNorm_div_rpow μ (f n) (hr n) ha (hint n)
    _ ≤ ((n : ℝ) ^ (-δ)) ^ r n :=
        Real.rpow_le_rpow (div_nonneg (rNorm_nonneg _ _ _) ha.le) hN (hr n).le
    _ = Real.exp (-δ * r n * Real.log n) := by
        rw [← Real.rpow_mul hn0.le, Real.rpow_def_of_pos hn0]
        congr 1; ring
    _ ≤ Real.exp (-(δ * Real.log n ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hlogr (mul_nonneg hδ.le hlog0)
        nlinarith only [h]
end Parking
