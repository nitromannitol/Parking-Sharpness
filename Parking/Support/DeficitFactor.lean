import Mathlib.Probability.Moments.Covariance

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The covariance of two bounded nonnegative variables is at most the product of their deficits. -/
theorem integral_mul_le_means_add_deficits (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (A B : ℝ)
    (hA : ∀ ω, 0 ≤ F ω ∧ F ω ≤ A) (hB : ∀ ω, 0 ≤ G ω ∧ G ω ≤ B) :
    (∫ ω, F ω * G ω ∂μ) ≤ (∫ ω, F ω ∂μ) * (∫ ω, G ω ∂μ) +
      ∫ ω, (A - F ω) * (B - G ω) ∂μ := by
  have hFL : MemLp F 2 μ := MemLp.of_bound hF.aestronglyMeasurable A
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hA ω).1]; exact (hA ω).2)
  have hGL : MemLp G 2 μ := MemLp.of_bound hG.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hB ω).1]; exact (hB ω).2)
  have hFi := hFL.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hGi := hGL.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hD : MemLp (fun ω => A - F ω) 2 μ := (memLp_const A).sub hFL
  have hE : MemLp (fun ω => B - G ω) 2 μ := (memLp_const B).sub hGL
  have he := covariance_eq_sub hD hE
  rw [covariance_const_sub_left hFi A, covariance_const_sub_right hGi B,
    neg_neg, covariance_eq_sub hFL hGL] at he
  change (∫ ω, F ω * G ω ∂μ) - (∫ ω, F ω ∂μ) * (∫ ω, G ω ∂μ) =
    (∫ ω, (A - F ω) * (B - G ω) ∂μ) -
      (∫ ω, A - F ω ∂μ) * (∫ ω, B - G ω ∂μ) at he
  have hn : 0 ≤ (∫ ω, A - F ω ∂μ) * (∫ ω, B - G ω ∂μ) := mul_nonneg (integral_nonneg fun ω => sub_nonneg.mpr (hA ω).2)
    (integral_nonneg fun ω => sub_nonneg.mpr (hB ω).2)
  linarith

/-- Relative lower means and a product-deficit estimate give an exponential reveal factor. -/
theorem integral_mul_factor_of_deficits (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (A B δ k : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hδ : 0 < δ) (hk : 0 ≤ k)
    (hA : ∀ ω, 0 ≤ F ω ∧ F ω ≤ A) (hB : ∀ ω, 0 ≤ G ω ∧ G ω ≤ B)
    (hMF : δ * A ≤ ∫ ω, F ω ∂μ) (hMG : δ * B ≤ ∫ ω, G ω ∂μ)
    (hdef : (∫ ω, (A - F ω) * (B - G ω) ∂μ) ≤ k * (A * B)) :
    (∫ ω, F ω * G ω ∂μ) ≤ Real.exp (k / δ ^ 2) *
      ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by
  let M := (∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ
  have hM : 0 ≤ M := mul_nonneg (integral_nonneg fun ω => (hA ω).1) (integral_nonneg fun ω => (hB ω).1)
  have hprod := mul_le_mul hMF hMG (mul_nonneg hδ.le hB0) ((mul_nonneg hδ.le hA0).trans hMF)
  have hAB : A * B ≤ M / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by dsimp only [M]; nlinarith [hprod])
  have hcost : k * (A * B) ≤ (k / δ ^ 2) * M :=
    (mul_le_mul_of_nonneg_left hAB hk).trans_eq (by ring)
  calc
    (∫ ω, F ω * G ω ∂μ) ≤ M + (∫ ω, (A - F ω) * (B - G ω) ∂μ) :=
      integral_mul_le_means_add_deficits μ F G hF hG A B hA hB
    _ ≤ M + (k / δ ^ 2) * M := add_le_add_right (hdef.trans hcost) M
    _ = (1 + k / δ ^ 2) * M := by ring
    _ ≤ Real.exp (k / δ ^ 2) * M := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (k / δ ^ 2)]) hM

/-- One relative influence bound suffices when the other observable is merely nonnegative. -/
theorem integral_mul_factor_one_sided (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (A B δ k : ℝ)
    (hA0 : 0 ≤ A) (hδ : 0 < δ) (hk : 0 ≤ k)
    (hA : ∀ ω, 0 ≤ F ω ∧ F ω ≤ A) (hB : ∀ ω, 0 ≤ G ω ∧ G ω ≤ B)
    (hMG : δ * B ≤ ∫ ω, G ω ∂μ) (hdef : B - (∫ ω, G ω ∂μ) ≤ k * B) :
    (∫ ω, F ω * G ω ∂μ) ≤ Real.exp (k / δ) *
      ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by
  have hfi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable A
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hA ω).1]; exact (hA ω).2)
  have hfgi : Integrable (fun ω => F ω * G ω) μ := Integrable.of_bound (hF.mul hG).aestronglyMeasurable (A * B)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA ω).1 (hB ω).1)]
      exact mul_le_mul (hA ω).2 (hB ω).2 (hB ω).1 hA0)
  have hF0 : 0 ≤ ∫ ω, F ω ∂μ := integral_nonneg fun ω => (hA ω).1
  have hG0 : 0 ≤ ∫ ω, G ω ∂μ := integral_nonneg fun ω => (hB ω).1
  have hBB : B ≤ (∫ ω, G ω ∂μ) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hcost : B - (∫ ω, G ω ∂μ) ≤ (k / δ) * ∫ ω, G ω ∂μ :=
    hdef.trans ((mul_le_mul_of_nonneg_left hBB hk).trans_eq (by ring))
  have hupper := integral_mono hfgi (hfi.mul_const B) (fun ω => mul_le_mul_of_nonneg_left (hB ω).2 (hA ω).1)
  rw [integral_mul_const] at hupper
  calc
    (∫ ω, F ω * G ω ∂μ) ≤ (∫ ω, F ω ∂μ) * B := hupper
    _ ≤ (∫ ω, F ω ∂μ) * ((1 + k / δ) * ∫ ω, G ω ∂μ) :=
      mul_le_mul_of_nonneg_left (by linarith) hF0
    _ = (1 + k / δ) * ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by ring
    _ ≤ Real.exp (k / δ) * ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (k / δ)]) (mul_nonneg hF0 hG0)
end Parking
