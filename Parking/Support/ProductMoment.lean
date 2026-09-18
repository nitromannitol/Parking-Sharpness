import Parking.Support.BoundedMoment

noncomputable section
namespace Parking
open MeasureTheory

/-- The moment norm on a product is the outer moment norm of the conditional moment norms. -/
theorem rNorm_prod {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × Ξ → ℝ) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun p => |F p| ^ r) (μ.prod ν)) :
    rNorm (μ.prod ν) r F = rNorm μ r (fun ω => rNorm ν r (fun ξ => F (ω, ξ))) := by
  have he (ω : Ω) : |rNorm ν r (fun ξ => F (ω, ξ))| ^ r = ∫ ξ, |F (ω, ξ)| ^ r ∂ν := by
    rw [abs_of_nonneg (rNorm_nonneg _ _ _), rNorm_rpow ν hr]
  change (∫ p, |F p| ^ r ∂(μ.prod ν)) ^ (1 / r) =
    (∫ ω, |rNorm ν r (fun ξ => F (ω, ξ))| ^ r ∂μ) ^ (1 / r)
  rw [integral_prod _ hi]
  simp_rw [he]

/-- Conditional moment norms are measurable in the retained parameter. -/
theorem measurable_conditional_rNorm {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (F : Ω × Ξ → ℝ) (hm : Measurable F)
    {r : ℝ} (hr : 0 < r) : Measurable (fun ω => rNorm ν r (fun ξ => F (ω, ξ))) := by
  have hpow := (measurable_rpow_const hr.le).comp hm.abs
  have hi := (hpow.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  exact (measurable_rpow_const (by positivity : (0 : ℝ) ≤ 1 / r)).comp hi

/-- Taking the outer norm of a root of conditional moments recovers the joint moment. -/
theorem rNorm_integral_root {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Ω × Ξ → ℝ) (hG : ∀ z, 0 ≤ G z) {r p : ℝ} (hr : 0 < r)
    (hi : Integrable (fun z => G z ^ p) (μ.prod ν)) :
    rNorm μ r (fun ω => (∫ ξ, G (ω, ξ) ^ p ∂ν) ^ (1 / r)) =
      (∫ z, G z ^ p ∂(μ.prod ν)) ^ (1 / r) := by
  have hn (ω : Ω) : 0 ≤ ∫ ξ, G (ω, ξ) ^ p ∂ν := integral_nonneg fun ξ => Real.rpow_nonneg (hG _) p
  have he (ω : Ω) : |(∫ ξ, G (ω, ξ) ^ p ∂ν) ^ (1 / r)| ^ r = ∫ ξ, G (ω, ξ) ^ p ∂ν := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hn ω) _), ← Real.rpow_mul (hn ω),
      one_div_mul_cancel hr.ne', Real.rpow_one]
  change (∫ ω, |(∫ ξ, G (ω, ξ) ^ p ∂ν) ^ (1 / r)| ^ r ∂μ) ^ (1 / r) = _
  simp_rw [he]
  rw [← integral_prod _ hi]
end Parking
