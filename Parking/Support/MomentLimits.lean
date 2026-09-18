/-
Moment norms, exponents and deterministic normalization.
-/
import Parking.Support.UpperStep
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
namespace Parking
open MeasureTheory
open scoped ENNReal

/-- Moment norms increase with the exponent under a probability measure. -/
theorem rNorm_mono_exponent {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (f : Ω → ℝ) (hm : AEStronglyMeasurable f μ)
    (hpi : Integrable (fun ω => |f ω| ^ p) μ) (hqi : Integrable (fun ω => |f ω| ^ q) μ) :
    rNorm μ p f ≤ rNorm μ q f := by
  rw [← eLpNorm_toReal_eq μ hp f hpi, ← eLpNorm_toReal_eq μ (hp.trans hpq) f hqi]
  exact ENNReal.toReal_mono (eLpNorm_ne_top μ (hp.trans hpq) f hqi)
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hm)

/-- Raising the moment norm back to its exponent recovers the moment. -/
theorem rNorm_rpow {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {r : ℝ} (hr : 0 < r) (f : Ω → ℝ) :
    rNorm μ r f ^ r = ∫ ω, |f ω| ^ r ∂μ := by
  rw [rNorm, ← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r),
    one_div_mul_cancel hr.ne', Real.rpow_one]

/-- Division by a deterministic scale preserves every finite moment. -/
theorem integrable_abs_div_rpow {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {r : ℝ} (hi : Integrable (fun ω => |f ω| ^ r) μ) (a : ℝ) :
    Integrable (fun ω => |f ω / a| ^ r) μ := by
  simpa only [abs_div, Real.div_rpow (abs_nonneg _) (abs_nonneg a)] using hi.div_const (|a| ^ r)

/-- The normalized moment in terms of the unnormalized moment norm. -/
theorem integral_abs_div_rpow {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {r : ℝ} (hr : 0 < r) (f : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∫ ω, |f ω / a| ^ r ∂μ = (rNorm μ r f / a) ^ r := by
  simp only [abs_div, abs_of_nonneg ha, Real.div_rpow (abs_nonneg _) ha]
  rw [integral_div, Real.div_rpow (rNorm_nonneg _ _ _) ha, rNorm_rpow μ hr f]
end Parking
