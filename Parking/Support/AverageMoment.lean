import Parking.Support.WeightedMoment
import Parking.Support.MomentLimits

noncomputable section
namespace Parking
open MeasureTheory

/-- An average of random variables obeying a common moment bound has the same bound. -/
theorem rNorm_average_le {ι Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Finset ι) (w : ι → ℝ) (F : ι → Ω → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hsum : ∑ i ∈ S, w i = 1)
    (hm : ∀ i ∈ S, Measurable (F i)) {r : ℝ} (hr : 1 ≤ r)
    (hi : ∀ i ∈ S, Integrable (fun ω => |F i ω| ^ r) μ)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ i ∈ S, rNorm μ r (F i) ≤ L) :
    Integrable (fun ω => |∑ i ∈ S, w i * F i ω| ^ r) μ ∧
      rNorm μ r (fun ω => ∑ i ∈ S, w i * F i ω) ≤ L := by
  classical
  have hr0 : 0 < r := by linarith
  let A : Ω → ℝ := fun ω => ∑ i ∈ S, w i * |F i ω|
  have hA := integral_weighted_rpow_le μ S w (fun i ω => |F i ω|) hw
    (fun _ _ _ => abs_nonneg _) (fun i hiS => (hm i hiS).abs) hr hi (L ^ r) (Real.rpow_nonneg hL r)
    (fun i hiS => by
      rw [← rNorm_rpow μ hr0 (F i)]
      exact Real.rpow_le_rpow (rNorm_nonneg _ _ _) (hb i hiS) hr0.le)
  have hA0 (ω : Ω) : 0 ≤ A ω := Finset.sum_nonneg fun i hiS => mul_nonneg (hw i hiS) (abs_nonneg _)
  have hpt (ω : Ω) : |∑ i ∈ S, w i * F i ω| ≤ A ω := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hiS
    rw [abs_mul, abs_of_nonneg (hw i hiS)]
  have hfi : Integrable (fun ω => |∑ i ∈ S, w i * F i ω| ^ r) μ := by
    apply hA.1.mono'
    · exact ((measurable_rpow_const hr0.le).comp
        (Finset.measurable_sum S fun i hiS => (hm i hiS).const_mul (w i)).abs).aestronglyMeasurable
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hpt ω) hr0.le
  have hI : (∫ ω, |∑ i ∈ S, w i * F i ω| ^ r ∂μ) ≤ L ^ r := by
    apply (integral_mono hfi hA.1 (fun ω => Real.rpow_le_rpow (abs_nonneg _) (hpt ω) hr0.le)).trans
    simpa only [hsum, Real.one_rpow, one_mul] using hA.2
  refine ⟨hfi, ?_⟩
  have hroot := Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r)
    hI (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [← Real.rpow_mul hL, mul_one_div, div_self hr0.ne', Real.rpow_one] at hroot
  exact hroot
end Parking
