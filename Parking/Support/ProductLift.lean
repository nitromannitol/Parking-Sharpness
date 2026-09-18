import Parking.Support.ProductMoment

noncomputable section
namespace Parking
open MeasureTheory

/-- Moment norms identify functions that agree almost everywhere. -/
theorem rNorm_congr_ae {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (r : ℝ)
    {f g : Ω → ℝ} (he : f =ᵐ[μ] g) : rNorm μ r f = rNorm μ r g := by
  unfold rNorm
  congr 1
  exact integral_congr_ae (he.mono fun _ h => congrArg (fun z : ℝ => |z| ^ r) h)

/-- The moment norm of a nonnegative constant under a probability law. -/
theorem rNorm_const {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) : rNorm μ r (fun _ : Ω => b) = b := by
  rw [rNorm, abs_of_nonneg hb, integral_const, probReal_univ, one_smul,
    ← Real.rpow_mul hb, mul_one_div, div_self hr.ne', Real.rpow_one]

/-- Minkowski's inequality for two bounded measurable functions. -/
theorem rNorm_bounded_add_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 1 ≤ r) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B D : ℝ) (hB : ∀ ω, |f ω| ≤ B) (hD : ∀ ω, |g ω| ≤ D) :
    rNorm μ r (fun ω => f ω + g ω) ≤ rNorm μ r f + rNorm μ r g := by
  have hr0 : 0 ≤ r := by linarith
  exact rNorm_add_le μ hr hf.aestronglyMeasurable hg.aestronglyMeasurable
    (integrable_abs_rpow_bounded μ f hf B hB hr0)
    (integrable_abs_rpow_bounded μ g hg D hD hr0)
    (integrable_abs_rpow_bounded μ _ (hf.add hg) (B + D)
      (fun ω => (abs_add_le _ _).trans (add_le_add (hB ω) (hD ω))) hr0)

/-- A conditional affine moment bound integrates to the corresponding joint bound. -/
theorem rNorm_prod_le_of_conditional {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × Ξ → ℝ) (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (D : ℝ) (hD : ∀ ω, Y ω ≤ D) {r : ℝ} (hr : 1 ≤ r)
    (hi : Integrable (fun z => |F z| ^ r) (μ.prod ν))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcond : ∀ ω, rNorm ν r (fun ξ => F (ω, ξ)) ≤ a * Y ω + b) :
    rNorm (μ.prod ν) r F ≤ a * rNorm μ r Y + b := by
  have hr0 : 0 < r := by linarith
  have hab (ω : Ω) : |a * Y ω| ≤ a * D := by
    rw [abs_of_nonneg (mul_nonneg ha (hY0 ω))]
    exact mul_le_mul_of_nonneg_left (hD ω) ha
  have hbi (ω : Ω) : |b| ≤ b := le_of_eq (abs_of_nonneg hb)
  have hsum (ω : Ω) : |a * Y ω + b| ≤ a * D + b :=
    (abs_add_le _ _).trans (add_le_add (hab ω) (hbi ω))
  rw [rNorm_prod μ ν F hr0 hi]
  have hmono := rNorm_mono μ hr0
    (ae_of_all μ fun ω => by
      rw [abs_of_nonneg (rNorm_nonneg ν r _), abs_of_nonneg (add_nonneg (mul_nonneg ha (hY0 ω)) hb)]
      exact hcond ω)
    (integrable_abs_rpow_bounded μ _ ((hY.const_mul a).add_const b) (a * D + b) hsum hr0.le)
  have hadd := rNorm_bounded_add_le μ hr (fun ω => a * Y ω) (fun _ => b)
    (hY.const_mul a) measurable_const (a * D) b hab hbi
  rw [rNorm_const_mul μ hr0 ha Y, rNorm_const μ hr0 hb] at hadd
  exact hmono.trans hadd
end Parking
