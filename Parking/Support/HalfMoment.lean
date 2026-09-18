import Parking.Support.ProductLift

noncomputable section
namespace Parking
open MeasureTheory

/-- A weighted half-moment bound is controlled by the square root of the full moment norm. -/
theorem half_moment_root_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (hm : Measurable X) {r : ℝ} (hr : 2 ≤ r)
    (hi : Integrable (fun ω => |X ω| ^ (r / 2)) μ)
    (hi' : Integrable (fun ω => |X ω| ^ r) μ)
    {W I : ℝ} (hW : 0 ≤ W) (hI : 0 ≤ I)
    (hb : I ≤ W ^ (r / 2) * ∫ ω, X ω ^ (r / 2) ∂μ) :
    I ^ (1 / r) ≤ Real.sqrt (W * rNorm μ r X) := by
  have hr0 : 0 < r := by linarith
  have hp0 : 0 < r / 2 := by linarith
  have hp1 : 1 ≤ r / 2 := by linarith
  have hmono := rNorm_mono_exponent μ hp1 (by linarith : r / 2 ≤ r) X hm.aestronglyMeasurable hi hi'
  have he : (∫ ω, X ω ^ (r / 2) ∂μ) = rNorm μ (r / 2) X ^ (r / 2) := by
    rw [rNorm_rpow μ hp0]
    exact integral_congr_ae (ae_of_all _ fun ω =>
      congrArg (fun z : ℝ => z ^ (r / 2)) (abs_of_nonneg (hX ω)).symm)
  rw [he, ← Real.mul_rpow hW (rNorm_nonneg μ (r / 2) X)] at hb
  have hb' : I ≤ (W * rNorm μ r X) ^ (r / 2) := hb.trans
    (Real.rpow_le_rpow (mul_nonneg hW (rNorm_nonneg _ _ _))
      (mul_le_mul_of_nonneg_left hmono hW) hp0.le)
  have hroot := Real.rpow_le_rpow hI hb' (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [← Real.rpow_mul (mul_nonneg hW (rNorm_nonneg _ _ _)),
    show r / 2 * (1 / r) = (1 : ℝ) / 2 by field_simp,
    ← Real.sqrt_eq_rpow] at hroot
  exact hroot
end Parking
