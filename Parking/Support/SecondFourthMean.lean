/- A first-moment lower bound from second and fourth moments. -/
import Parking.Support.UpperStep
import LatticeProb.Prob.PaleyZygmund
import LatticeProb.Prob.Moments

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

theorem abs_mean_lower_of_second_fourth {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X : Ω → ℝ) (hm : Measurable X)
    (h4 : Integrable (fun ω => X ω ^ 4) Q) {a b V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hsecond : (∫ ω, X ω ^ 2 ∂Q) = a * V)
    (hfourth : (∫ ω, X ω ^ 4 ∂Q) ≤ b * V ^ 2) :
    (a ^ 2 / (4 * b) * Real.sqrt (a / 2)) * Real.sqrt V ≤ ∫ ω, |X ω| ∂Q := by
  let S : Set Ω := {ω | (1 / 2 : ℝ) * (∫ z, X z ^ 2 ∂Q) < X ω ^ 2}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (hm.pow_const 2)
  have h22 : Integrable (fun ω => (X ω ^ 2) ^ 2) Q := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by omega] using h4
  have hpz := paley_zygmund Q (hm.pow_const 2) (fun ω => sq_nonneg (X ω)) h22
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hq0 : 0 ≤ Q.real S := measureReal_nonneg
  have hp : a ^ 2 / (4 * b) ≤ Q.real S := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * b)).mpr
    have hf := mul_le_mul_of_nonneg_right hfourth hq0
    change (1 - (1 / 2 : ℝ)) ^ 2 * (∫ ω, X ω ^ 2 ∂Q) ^ 2 ≤
      (∫ ω, (X ω ^ 2) ^ 2 ∂Q) * Q.real S at hpz
    simp only [← pow_mul, show (2 : ℕ) * 2 = 4 by omega, hsecond] at hpz
    have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
    nlinarith [hpz, hf]
  have hXi : Integrable X Q := integrable_pow_of_integrable_pow_four
    hm.aestronglyMeasurable h4 (p := 1) (by norm_num) |>.congr (Filter.Eventually.of_forall fun ω => by simp)
  have hdom (ω : Ω) : S.indicator (fun _ => Real.sqrt (a * V / 2)) ω ≤ |X ω| := by
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hh : a * V / 2 < X ω ^ 2 := by
        change (1 / 2 : ℝ) * (∫ z, X z ^ 2 ∂Q) < X ω ^ 2 at hω
        rw [hsecond] at hω
        linarith
      have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a * V / 2)
      nlinarith [Real.sqrt_nonneg (a * V / 2), abs_nonneg (X ω), sq_abs (X ω)]
    · rw [Set.indicator_of_notMem hω]
      exact abs_nonneg _
  have hi := integral_mono ((integrable_const (Real.sqrt (a * V / 2))).indicator hS) hXi.abs hdom
  rw [integral_indicator_const _ hS] at hi
  have hs : Real.sqrt (a * V / 2) = Real.sqrt (a / 2) * Real.sqrt V := by
    rw [show a * V / 2 = (a / 2) * V by ring, Real.sqrt_mul (by positivity)]
  rw [hs] at hi
  have hp' := mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.sqrt_nonneg (a / 2)) (Real.sqrt_nonneg V))
  calc (a ^ 2 / (4 * b) * Real.sqrt (a / 2)) * Real.sqrt V
      ≤ Q.real S * (Real.sqrt (a / 2) * Real.sqrt V) := by
        simpa only [mul_assoc] using hp'
    _ ≤ _ := by simpa only [smul_eq_mul] using hi

end Parking
