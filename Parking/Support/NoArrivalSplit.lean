import Parking.Support.NoArrivalWeight
import Parking.Support.MomentLowerTail

noncomputable section
namespace Parking
open MeasureTheory

/-- Split a no-arrival event according to whether its compensator is small. -/
theorem measure_flag_le_lower_tail {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Bool) (L : Ω → ℝ)
    (hF : Measurable F) (hL : Measurable L)
    (hi : Integrable (fun ω => if F ω then Real.exp (L ω) else 0) μ)
    (hb : (∫ ω, if F ω then Real.exp (L ω) else 0 ∂μ) ≤ 1) (a : ℝ) :
    (μ {ω | F ω = true}).toReal ≤ (μ {ω | L ω < a}).toReal + Real.exp (-a) := by
  classical
  let S := {ω | F ω = true}
  let B := {ω | L ω < a}
  let W : Ω → ℝ := fun ω => if F ω then Real.exp (L ω) else 0
  have hS : MeasurableSet S := hF (measurableSet_singleton true)
  have hB : MeasurableSet B := measurableSet_lt hL measurable_const
  have hiS : Integrable (S.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hS
  have hiB : Integrable (B.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hB
  have hW (ω : Ω) : 0 ≤ W ω := by dsimp [W]; split <;> positivity
  have hp (ω : Ω) : S.indicator (fun _ => (1 : ℝ)) ω ≤
      B.indicator (fun _ => (1 : ℝ)) ω + Real.exp (-a) * W ω := by
    by_cases hf : F ω = true
    · have hs : ω ∈ S := hf
      rw [Set.indicator_of_mem hs]
      by_cases hl : L ω < a
      · have hx : ω ∈ B := hl
        rw [Set.indicator_of_mem hx]
        exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (hW ω))
      · have hx : ω ∉ B := hl
        rw [Set.indicator_of_notMem hx, zero_add]
        dsimp only [W]
        rw [if_pos hf, ← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
    · have hs : ω ∉ S := hf
      rw [Set.indicator_of_notMem hs]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
        (mul_nonneg (Real.exp_pos _).le (hW ω))
  have h := integral_mono hiS (hiB.add (hi.const_mul (Real.exp (-a)))) hp
  change (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤
    ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω + Real.exp (-a) * (if F ω then Real.exp (L ω) else 0) ∂μ at h
  rw [integral_add hiB (hi.const_mul _), integral_const_mul, integral_indicator_const (1 : ℝ) hS,
    integral_indicator_const (1 : ℝ) hB] at h
  simp only [smul_eq_mul, mul_one] at h
  apply h.trans
  apply add_le_add (le_refl _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (Real.exp_pos (-a)).le
end Parking
