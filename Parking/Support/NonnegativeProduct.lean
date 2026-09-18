/- Product integrability from integrable nonnegative section bounds. -/
import Mathlib

noncomputable section
namespace Parking
open MeasureTheory

/-- An integrable bound on the section integrals gives product integrability
and the corresponding expectation bound for a nonnegative measurable function. -/
theorem integral_prod_le_of_sections {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν] (F : Ω × Ξ → ℝ) (hm : Measurable F)
    (hF : ∀ z, 0 ≤ F z) (hi : ∀ ω, Integrable (fun ξ => F (ω, ξ)) ν)
    (B : Ω → ℝ) (hB : Integrable B μ) (hbound : ∀ ω, ∫ ξ, F (ω, ξ) ∂ν ≤ B ω) :
    Integrable F (μ.prod ν) ∧ (∫ z, F z ∂(μ.prod ν)) ≤ ∫ ω, B ω ∂μ := by
  have hinner : Integrable (fun ω => ∫ ξ, F (ω, ξ) ∂ν) μ := by
    refine hB.mono' (hm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ξ => hF (ω, ξ))]
      exact hbound ω
  have he : ∀ (ω : Ω) (ξ : Ξ), ‖F (ω, ξ)‖ = F (ω, ξ) :=
    fun ω ξ => by rw [Real.norm_eq_abs, abs_of_nonneg (hF (ω, ξ))]
  have hprod : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi, ?_⟩
    simpa only [he] using hinner
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod]
  exact integral_mono hinner hB hbound

end Parking
