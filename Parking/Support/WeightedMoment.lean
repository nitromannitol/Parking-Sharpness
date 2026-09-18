import Parking.Support.Lp

noncomputable section
namespace Parking
open MeasureTheory

/-- A finite nonnegative weighted sum inherits the common moment bound of its summands. -/
theorem integral_weighted_rpow_le {ι Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (w : ι → ℝ) (X : ι → Ω → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hX : ∀ i ∈ S, ∀ ω, 0 ≤ X i ω)
    (hm : ∀ i ∈ S, Measurable (X i)) {p : ℝ} (hp : 1 ≤ p)
    (hi : ∀ i ∈ S, Integrable (fun ω => X i ω ^ p) μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i ∈ S, ∫ ω, X i ω ^ p ∂μ ≤ M) :
    Integrable (fun ω => (∑ i ∈ S, w i * X i ω) ^ p) μ ∧
      (∫ ω, (∑ i ∈ S, w i * X i ω) ^ p ∂μ) ≤ (∑ i ∈ S, w i) ^ p * M := by
  classical
  let W : ℝ := ∑ i ∈ S, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hnorm : ∑ i ∈ S, w i / W ≤ 1 := by
    rw [← Finset.sum_div]
    change W / W ≤ 1
    by_cases hz : W = 0
    · simp [hz]
    · rw [div_self hz]
  let D : Ω → ℝ := fun ω => W ^ p * ∑ i ∈ S, (w i / W) * X i ω ^ p
  have hDi : Integrable D μ :=
    (integrable_finsetSum _ (fun i hiS => (hi i hiS).const_mul (w i / W))).const_mul (W ^ p)
  have hpt (ω : Ω) : (∑ i ∈ S, w i * X i ω) ^ p ≤ D ω :=
    rpow_weighted_sum_le S w (fun i => X i ω) hw (fun i hiS => hX i hiS ω) hp
  have hnn (ω : Ω) : 0 ≤ ∑ i ∈ S, w i * X i ω :=
    Finset.sum_nonneg fun i hiS => mul_nonneg (hw i hiS) (hX i hiS ω)
  have hfi : Integrable (fun ω => (∑ i ∈ S, w i * X i ω) ^ p) μ := by
    apply hDi.mono'
    · exact ((measurable_rpow_const (by linarith : 0 ≤ p)).comp
        (Finset.measurable_sum S fun i hiS => (hm i hiS).const_mul (w i))).aestronglyMeasurable
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hnn ω) p)]
        exact hpt ω
  refine ⟨hfi, (integral_mono hfi hDi hpt).trans ?_⟩
  change (∫ ω, W ^ p * ∑ i ∈ S, (w i / W) * X i ω ^ p ∂μ) ≤ W ^ p * M
  rw [integral_const_mul, integral_finsetSum _ (fun i hiS => (hi i hiS).const_mul _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hW p)
  calc
    _ ≤ ∑ i ∈ S, (w i / W) * M := by
      apply Finset.sum_le_sum
      intro i hiS
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound i hiS) (div_nonneg (hw i hiS) hW)
    _ = (∑ i ∈ S, w i / W) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ M := by nlinarith
end Parking
