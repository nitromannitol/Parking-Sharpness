import Parking.Support.ProductMoment

noncomputable section
namespace Parking
open MeasureTheory

/-- Every nonnegative moment of a bounded nonnegative measurable function is integrable. -/
theorem integrable_rpow_bounded_nonneg {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (hm : Measurable F)
    (h0 : ∀ ω, 0 ≤ F ω) (B : ℝ) (hB : ∀ ω, F ω ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => F ω ^ r) μ := by
  have hab (ω : Ω) : |F ω| ≤ B := (abs_of_nonneg (h0 ω)).le.trans (hB ω)
  have he : (fun ω => |F ω| ^ r) = (fun ω => F ω ^ r) :=
    funext fun ω => congrArg (fun z : ℝ => z ^ r) (abs_of_nonneg (h0 ω))
  exact he ▸ integrable_abs_rpow_bounded μ F hm B hab hr

/-- A root of conditional moments is measurable and uniformly bounded. -/
theorem bounded_conditional_moment_root {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (F : Ω × Ξ → ℝ) (hm : Measurable F)
    (h0 : ∀ z, 0 ≤ F z) (B : ℝ) (hB : ∀ z, F z ≤ B) {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) :
    Measurable (fun ω => (∫ ξ, F (ω, ξ) ^ p ∂ν) ^ (1 / r)) ∧
      ∀ ω, 0 ≤ (∫ ξ, F (ω, ξ) ^ p ∂ν) ^ (1 / r) ∧
        (∫ ξ, F (ω, ξ) ^ p ∂ν) ^ (1 / r) ≤ (B ^ p) ^ (1 / r) := by
  have hpmeas := (measurable_rpow_const hp).comp hm
  have hI := (hpmeas.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  refine ⟨(measurable_rpow_const (by positivity : (0 : ℝ) ≤ 1 / r)).comp hI, fun ω => ?_⟩
  have hn : 0 ≤ ∫ ξ, F (ω, ξ) ^ p ∂ν := integral_nonneg fun ξ => Real.rpow_nonneg (h0 _) p
  refine ⟨Real.rpow_nonneg hn _, Real.rpow_le_rpow hn ?_ (by positivity)⟩
  have hi := integrable_rpow_bounded_nonneg ν (fun ξ => F (ω, ξ))
    (hm.comp (measurable_const.prodMk measurable_id)) (fun ξ => h0 _) B (fun ξ => hB _) hp
  have hb := integral_mono hi (integrable_const (B ^ p))
    (fun ξ => Real.rpow_le_rpow (h0 _) (hB _) hp)
  simpa only [integral_const, probReal_univ, one_smul] using hb
end Parking
