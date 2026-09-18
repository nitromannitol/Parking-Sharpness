/- Jensen's inequality converts a finite exponential moment to a mean bound. -/
import Mathlib

noncomputable section
namespace Parking
open MeasureTheory

theorem mean_le_of_exp_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hm : Measurable X) (hn : ∀ ω, 0 ≤ X ω) {τ B : ℝ} (hτ : 0 < τ)
    (hi : Integrable (fun ω => Real.exp (τ * X ω)) μ)
    (hb : (∫ ω, Real.exp (τ * X ω) ∂μ) ≤ Real.exp B) :
    Integrable X μ ∧ τ * (∫ ω, X ω ∂μ) ≤ B := by
  have hXi : Integrable X μ := by
    refine (hi.const_mul τ⁻¹).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hn ω), ← div_eq_inv_mul]
    apply (le_div_iff₀ hτ).mpr
    have h := Real.add_one_le_exp (τ * X ω)
    nlinarith
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun ω => Set.mem_univ (τ * X ω))
    (hXi.const_mul τ) hi
  rw [integral_const_mul] at hj
  exact ⟨hXi, Real.exp_le_exp.mp (hj.trans hb)⟩

end Parking
