import Mathlib.Probability.Moments.Variance

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory

/-- A bounded nonnegative influence controls both its centered increment and its variance. -/
theorem centered_influence_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f G : Ω → ℝ) (m B : ℝ)
    (hf : Measurable f) (hG : Measurable G)
    (h : ∀ ω, 0 ≤ f ω - m ∧ f ω - m ≤ G ω ∧ G ω ≤ B) :
    (∀ ω, |f ω - ∫ a, f a ∂μ| ≤ B) ∧
      (∫ ω, (f ω - ∫ a, f a ∂μ) ^ 2 ∂μ) ≤ ∫ ω, G ω ^ 2 ∂μ := by
  let g : Ω → ℝ := fun ω => f ω - m
  have hg : Measurable g := hf.sub_const m
  have hgn (ω) : 0 ≤ g ω := (h ω).1
  have hgb (ω) : g ω ≤ B := (h ω).2.1.trans (h ω).2.2
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hgn ω)]; exact hgb ω)
  have hfi : Integrable f μ := by
    have H : Integrable (fun ω => g ω + m) μ := hi.add (integrable_const m)
    have he : (fun ω => g ω + m) = f := funext fun ω => sub_add_cancel (f ω) m
    rw [he] at H
    exact H
  have hmean : ∫ ω, g ω ∂μ = (∫ ω, f ω ∂μ) - m := by
    rw [show g = fun ω => f ω - m from rfl, integral_sub hfi (integrable_const m)]
    simp
  have hm0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg hgn
  have hmB : ∫ ω, g ω ∂μ ≤ B := by
    simpa using integral_mono hi (integrable_const B) hgb
  have hc (ω) : f ω - ∫ a, f a ∂μ = g ω - ∫ a, g a ∂μ := by
    rw [hmean]
    dsimp [g]
    ring
  constructor
  · intro ω
    rw [hc]
    exact abs_le.mpr ⟨by linarith [hgn ω], by linarith [hgb ω]⟩
  · simp_rw [hc]
    rw [← variance_eq_integral hg.aemeasurable]
    refine (variance_le_expectation_sq hg.aestronglyMeasurable).trans ?_
    have hgi2 : Integrable (fun ω => g ω ^ 2) μ := Integrable.of_bound
      (hg.pow_const 2).aestronglyMeasurable (B ^ 2) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hgn ω) (hgb ω) 2)
    have hGi2 : Integrable (fun ω => G ω ^ 2) μ := Integrable.of_bound
      (hG.pow_const 2).aestronglyMeasurable (B ^ 2) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ ((hgn ω).trans (h ω).2.1) (h ω).2.2 2)
    exact integral_mono hgi2 hGi2 fun ω => pow_le_pow_left₀ (hgn ω) (h ω).2.1 2
end Parking
