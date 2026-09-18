import Parking.Support.WeightedMoment
import Parking.Support.MomentTail

noncomputable section
namespace Parking
open MeasureTheory

/-- Nonnegative weighted sums inherit a common moment norm bound. -/
theorem rNorm_weighted_sum_le {Ω ι : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι) (w : ι → ℝ) (F : ι → Ω → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hF : ∀ i ∈ S, ∀ ω, 0 ≤ F i ω)
    (hm : ∀ i ∈ S, Measurable (F i)) {r : ℝ} (hr : 1 ≤ r)
    (hi : ∀ i ∈ S, Integrable (fun ω => F i ω ^ r) μ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i ∈ S, rNorm μ r (F i) ≤ M) :
    Integrable (fun ω => (∑ i ∈ S, w i * F i ω) ^ r) μ ∧
      rNorm μ r (fun ω => ∑ i ∈ S, w i * F i ω) ≤ (∑ i ∈ S, w i) * M := by
  have hr0 : 0 < r := by linarith
  have hmi (i : ι) (hiS : i ∈ S) : (∫ ω, F i ω ^ r ∂μ) ≤ M ^ r := by
    have h := Real.rpow_le_rpow (rNorm_nonneg μ r (F i)) (hb i hiS) hr0.le
    unfold rNorm at h
    simp only [abs_of_nonneg (hF i hiS _)] at h
    rw [← Real.rpow_mul (integral_nonneg fun ω => Real.rpow_nonneg (hF i hiS ω) r),
      one_div_mul_cancel hr0.ne', Real.rpow_one] at h
    exact h
  have h := integral_weighted_rpow_le μ S w F hw hF hm hr hi (M ^ r) (Real.rpow_nonneg hM r) hmi
  refine ⟨h.1, ?_⟩
  have hW : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg hw
  have hX (ω : Ω) : 0 ≤ ∑ i ∈ S, w i * F i ω := Finset.sum_nonneg fun i hiS => mul_nonneg (hw i hiS) (hF i hiS ω)
  unfold rNorm
  simp only [abs_of_nonneg (hX _)]
  have hbnd := Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (hX ω) r) h.2 (by positivity : 0 ≤ 1 / r)
  apply hbnd.trans_eq
  rw [← Real.mul_rpow hW hM, ← Real.rpow_mul (mul_nonneg hW hM), mul_one_div_cancel hr0.ne', Real.rpow_one]
end Parking
