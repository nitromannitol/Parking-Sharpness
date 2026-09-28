import Mathlib

/-!
# Integrating an event probability against countable fiber probabilities

If a countable-valued measurable map `F` splits an event `E` so that on each fiber `{F = m}`
the event `E` carries a known fraction `w m` of the fiber's mass, then the total probability
of `E` is the expectation of `w ∘ F`. This lets a probability be computed by conditioning on
`F` and integrating the conditional probabilities `w`.
-/

noncomputable section
namespace Parking
open MeasureTheory

/-- If `E` occupies fraction `w m` of the mass of each fiber `{F = m}` of a countable-valued
measurable map `F`, then `μ.real E = ∫ w (F ω) ∂μ`, by summing `w m` weighted by fiber mass
over the countable range of `F` (`integral_countable`). -/
theorem probability_eq_integral_of_fibers {Ω M : Type*} [MeasurableSpace Ω]
    [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → M) (hF : Measurable F)
    (E : Set Ω) (w : M → ℝ)
    (hw0 : ∀ m, 0 ≤ w m) (hw1 : ∀ m, w m ≤ 1)
    (hfib : ∀ m, μ.real (E ∩ {ω | F ω = m}) = w m * μ.real {ω | F ω = m}) :
    μ.real E = ∫ ω, w (F ω) ∂μ := by
  have hw : Measurable w := measurable_of_countable w
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  have hi : Integrable w (μ.map F) := (integrable_const (1 : ℝ)).mono'
    hw.aestronglyMeasurable (Filter.Eventually.of_forall fun m => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 m)]
      exact hw1 m)
  have hleft := integral_countable (integrable_const (1 : ℝ) (μ := (μ.restrict E).map F))
  have heleft : (∫ m, (1 : ℝ) ∂((μ.restrict E).map F)) = μ.real E := by
    rw [integral_const]
    simp only [measureReal_def, Measure.map_apply hF MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
  rw [heleft] at hleft
  rw [← integral_map hF.aemeasurable hw.aestronglyMeasurable, integral_countable hi, hleft]
  apply tsum_congr
  intro m
  simp only [smul_eq_mul, mul_one, measureReal_def,
    Measure.map_apply hF (measurableSet_singleton m),
    Measure.restrict_apply (hF (measurableSet_singleton m))]
  have hf := hfib m
  change (μ ({ω | F ω = m} ∩ E)).toReal = (μ {ω | F ω = m}).toReal * w m
  rw [Set.inter_comm]
  exact hf.trans (mul_comm _ _)

end Parking
