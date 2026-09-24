import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace Parking
open MeasureTheory

/-- A discounted event estimate becomes an ordinary estimate outside a large-cost event. -/
theorem measure_event_le_discount_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (W : Ω → ℝ) (hW : Measurable W) (c : ℝ) (hc : 0 ≤ c)
    (D : Ω → ℝ) (hD : ∀ ω, 0 ≤ D ω) (hi : Integrable D μ)
    (hED : ∀ ω ∈ E, D ω = Real.exp (-c * W ω)) (M : ℝ) (hM : (∫ ω, D ω ∂μ) ≤ M) (a : ℝ) :
    (μ E).toReal ≤ Real.exp (c * a) * M + (μ {ω | a < W ω}).toReal := by
  classical
  let B := {ω | a < W ω}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hW
  have hiE : Integrable (E.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hE
  have hiB : Integrable (B.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hB
  have hp (ω : Ω) : E.indicator (fun _ => (1 : ℝ)) ω ≤
      Real.exp (c * a) * D ω + B.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      by_cases hb : ω ∈ B
      · rw [Set.indicator_of_mem hb]
        exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (hD ω))
      · rw [Set.indicator_of_notMem hb, add_zero, hED ω he, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        have hw : W ω ≤ a := le_of_not_gt hb
        nlinarith [mul_le_mul_of_nonneg_left hw hc]
    · rw [Set.indicator_of_notMem he]
      exact add_nonneg (mul_nonneg (Real.exp_pos _).le (hD ω))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h := integral_mono hiE ((hi.const_mul _).add hiB) hp
  change (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤
    ∫ ω, Real.exp (c * a) * D ω + B.indicator (fun _ => (1 : ℝ)) ω ∂μ at h
  rw [integral_add (hi.const_mul _) hiB, integral_const_mul,
    integral_indicator_const (1 : ℝ) hE, integral_indicator_const (1 : ℝ) hB] at h
  simp only [smul_eq_mul, mul_one] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le) le_rfl)
end Parking
