import Parking.Support.MomentLimits
import Parking.Support.Lp

noncomputable section
namespace Parking
open MeasureTheory

/-- Every nonnegative real moment of a bounded measurable functional is integrable. -/
theorem integrable_abs_rpow_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ ω, |f ω| ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => |f ω| ^ r) μ := by
  apply Integrable.of_bound ((measurable_rpow_const hr).comp hf.abs).aestronglyMeasurable (B ^ r)
  exact ae_of_all _ fun ω => by
    change ‖|f ω| ^ r‖ ≤ B ^ r
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hB ω) hr

/-- A uniform bound also bounds every positive moment norm under a probability law. -/
theorem rNorm_le_of_abs_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ ω, |f ω| ≤ B)
    {r : ℝ} (hr : 0 < r) : rNorm μ r f ≤ B := by
  have hi := integrable_abs_rpow_bounded μ f hf B hB hr.le
  have h := integral_mono hi (integrable_const (B ^ r))
    (fun ω => Real.rpow_le_rpow (abs_nonneg _) (hB ω) hr.le)
  simp only [integral_const, probReal_univ, one_smul] at h
  have hb := Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r)
    h (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [← Real.rpow_mul hB0, mul_one_div, div_self hr.ne', Real.rpow_one] at hb
  exact hb
end Parking
