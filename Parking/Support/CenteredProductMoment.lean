import Parking.Support.ProductLift

noncomputable section
namespace Parking
open MeasureTheory

/-- A nonnegative power of the absolute constant has its usual moment norm. -/
theorem rNorm_const_abs {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (b : ℝ) : rNorm μ r (fun _ : Ω => b) = |b| := by
  rw [rNorm, integral_const, probReal_univ, one_smul, ← Real.rpow_mul (abs_nonneg b),
    mul_one_div, div_self hr.ne', Real.rpow_one]

/-- Adding an independent product coordinate does not alter the norm of a bounded function. -/
theorem rNorm_prod_fst_bounded {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hm : Measurable Y) (B : ℝ) (hB : ∀ ω, |Y ω| ≤ B) {r : ℝ} (hr : 0 < r) :
    rNorm (μ.prod ν) r (fun z => Y z.1) = rNorm μ r Y := by
  have hi := integrable_abs_rpow_bounded (μ.prod ν) (fun z => Y z.1) (hm.comp measurable_fst)
    B (fun z => hB z.1) hr.le
  rw [rNorm_prod μ ν _ hr hi]
  simp_rw [rNorm_const_abs ν hr]
  unfold rNorm
  simp only [abs_abs]

/-- A bounded product observable splits into a centered retained part and its remaining noise. -/
theorem rNorm_bounded_centered_decomposition {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × Ξ → ℝ) (Y : Ω → ℝ) (hF : Measurable F) (hY : Measurable Y)
    (B D : ℝ) (hB : ∀ z, |F z| ≤ B) (hD : ∀ ω, |Y ω| ≤ D) (b : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    rNorm (μ.prod ν) r (fun z => F z - b) ≤ rNorm μ r (fun ω => Y ω - b) +
      rNorm (μ.prod ν) r (fun z => F z - Y z.1) := by
  have hDb (ω : Ω) : |Y ω - b| ≤ D + |b| := (abs_sub _ _).trans (add_le_add (hD ω) le_rfl)
  have hdiff (z : Ω × Ξ) : |F z - Y z.1| ≤ B + D := (abs_sub _ _).trans (add_le_add (hB z) (hD z.1))
  have h := rNorm_bounded_add_le (μ.prod ν) hr (fun z => Y z.1 - b) (fun z => F z - Y z.1)
    ((hY.comp measurable_fst).sub_const b) (hF.sub (hY.comp measurable_fst))
    (D + |b|) (B + D) (fun z => hDb z.1) hdiff
  have he : (fun z : Ω × Ξ => (Y z.1 - b) + (F z - Y z.1)) = (fun z => F z - b) := funext fun _ => by ring
  rw [he, rNorm_prod_fst_bounded μ ν (fun ω => Y ω - b) (hY.sub_const b) _ hDb (by linarith)] at h
  exact h
end Parking
