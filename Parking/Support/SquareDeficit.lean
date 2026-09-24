import Parking.Support.DeficitFactor

noncomputable section
namespace Parking
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A two-step relative lower bound controls the loss from its baseline. -/
theorem square_relative_deficit (e A a : ℝ) (hA : 0 ≤ A) (ha : e ^ 2 * A ≤ a) :
    0 ≤ a ∧ A - a ≤ 2 * (1 - e) * A := by
  constructor
  · exact (mul_nonneg (sq_nonneg e) hA).trans ha
  · nlinarith [mul_nonneg (sq_nonneg (1 - e)) hA]

/-- A pointwise squared relative bound gives the same lower bound on the mean. -/
theorem integral_square_relative_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hFi : Integrable F μ) (A e δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (he : δ ≤ e) (hF : ∀ ω, e ^ 2 * A ≤ F ω) :
    δ ^ 2 * A ≤ ∫ ω, F ω ∂μ := by
  have h := integral_mono (integrable_const (e ^ 2 * A)) hFi hF
  simp only [integral_const, probReal_univ, one_smul] at h
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ he 2) hA).trans h

/-- Two squared relative envelopes give a product factor with the product of their hitting deficits. -/
theorem integral_square_relative_factor (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (A B e f δ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ)
    (he : δ ≤ e ∧ e ≤ 1) (hf : δ ≤ f ∧ f ≤ 1)
    (hFA : ∀ ω, e ^ 2 * A ≤ F ω ∧ F ω ≤ A)
    (hGB : ∀ ω, f ^ 2 * B ≤ G ω ∧ G ω ≤ B) :
    (∫ ω, F ω * G ω ∂μ) ≤ Real.exp ((4 / δ ^ 4) * (1 - e) * (1 - f)) *
      ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by
  have hFn (ω) := (square_relative_deficit e A (F ω) hA (hFA ω).1).1
  have hGn (ω) := (square_relative_deficit f B (G ω) hB (hGB ω).1).1
  have hFi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable A
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hFn ω)]; exact (hFA ω).2)
  have hGi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hGn ω)]; exact (hGB ω).2)
  have hMF := integral_square_relative_lower μ F hFi A e δ hA hδ.le he.1 (fun ω => (hFA ω).1)
  have hMG := integral_square_relative_lower μ G hGi B f δ hB hδ.le hf.1 (fun ω => (hGB ω).1)
  have hdefi : Integrable (fun ω => (A - F ω) * (B - G ω)) μ :=
    Integrable.of_bound ((measurable_const.sub hF).mul (measurable_const.sub hG)).aestronglyMeasurable (A * B)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (hFA ω).2) (sub_nonneg.mpr (hGB ω).2))]
        exact mul_le_mul (by linarith [hFn ω]) (by linarith [hGn ω]) (sub_nonneg.mpr (hGB ω).2) hA)
  have hdef : (∫ ω, (A - F ω) * (B - G ω) ∂μ) ≤ (4 * (1 - e) * (1 - f)) * (A * B) := by
    have hp (ω : Ω) : (A - F ω) * (B - G ω) ≤ (4 * (1 - e) * (1 - f)) * (A * B) := by
      have ha := (square_relative_deficit e A (F ω) hA (hFA ω).1).2
      have hb := (square_relative_deficit f B (G ω) hB (hGB ω).1).2
      exact (mul_le_mul ha hb (sub_nonneg.mpr (hGB ω).2)
        (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr he.2)) hA)).trans_eq (by ring)
    simpa only [integral_const, probReal_univ, one_smul] using integral_mono hdefi (integrable_const _) hp
  have h := integral_mul_factor_of_deficits μ F G hF hG A B (δ ^ 2) (4 * (1 - e) * (1 - f))
    hA hB (sq_pos_of_pos hδ) (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr he.2)) (sub_nonneg.mpr hf.2)) (fun ω => ⟨hFn ω, (hFA ω).2⟩)
    (fun ω => ⟨hGn ω, (hGB ω).2⟩) hMF hMG hdef
  have heq : (4 * (1 - e) * (1 - f)) / (δ ^ 2) ^ 2 = (4 / δ ^ 4) * (1 - e) * (1 - f) := by ring
  rwa [heq] at h

/-- At one target only the other site's relative envelope is needed. -/
theorem integral_square_relative_one_sided (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (A B e δ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) (he : δ ≤ e ∧ e ≤ 1)
    (hFA : ∀ ω, 0 ≤ F ω ∧ F ω ≤ A)
    (hGB : ∀ ω, e ^ 2 * B ≤ G ω ∧ G ω ≤ B) :
    (∫ ω, F ω * G ω ∂μ) ≤ Real.exp ((2 / δ ^ 2) * (1 - e)) *
      ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by
  have hGn (ω) := (square_relative_deficit e B (G ω) hB (hGB ω).1).1
  have hGi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hGn ω)]; exact (hGB ω).2)
  have hMG := integral_square_relative_lower μ G hGi B e δ hB hδ.le he.1 (fun ω => (hGB ω).1)
  have hdef : B - (∫ ω, G ω ∂μ) ≤ (2 * (1 - e)) * B := by
    have h := integral_mono (integrable_const (B - 2 * (1 - e) * B)) hGi
      (fun ω => by linarith [(square_relative_deficit e B (G ω) hB (hGB ω).1).2])
    simp only [integral_const, probReal_univ, one_smul] at h
    linarith
  have h := integral_mul_factor_one_sided μ F G hF hG A B (δ ^ 2) (2 * (1 - e)) hA (sq_pos_of_pos hδ)
    (mul_nonneg (by norm_num) (sub_nonneg.mpr he.2)) hFA (fun ω => ⟨hGn ω, (hGB ω).2⟩) hMG hdef
  have heq : (2 * (1 - e)) / δ ^ 2 = (2 / δ ^ 2) * (1 - e) := by ring
  rwa [heq] at h
end Parking
