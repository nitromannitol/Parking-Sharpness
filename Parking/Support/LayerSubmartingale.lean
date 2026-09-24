import Parking.Support.LayerReward

noncomputable section
namespace Parking
open MeasureTheory

/-- A bounded process with increasing fresh-layer sections has increasing expectations. -/
theorem layer_submartingale_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (V : (ℕ → α) → ℕ → ℝ)
    (hm : ∀ n, Measurable (fun ω => V ω n)) (B : ℝ) (hB : ∀ ω n, ‖V ω n‖ ≤ B)
    (T : ℕ) (hs : ∀ n < T, ∀ ω,
      V ω n ≤ ∫ a, V (Function.update ω n a) (n + 1) ∂μ) :
    ∫ ω, V ω 0 ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫ ω, V ω T ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  have hstep (n : ℕ) (hn : n < T) :
      (∫ ω, V ω n ∂(Measure.infinitePi fun _ : ℕ => μ)) ≤
        ∫ ω, V ω (n + 1) ∂(Measure.infinitePi fun _ : ℕ => μ) := by
    have h := integral_le_of_bounded_layer_sections μ
      (fun ω => -V ω (n + 1)) (fun ω => -V ω n) (hm (n + 1)).neg (hm n).neg B B
      (fun ω => by simpa only [norm_neg] using hB ω (n + 1))
      (fun ω => by simpa only [norm_neg] using hB ω n) n
      (fun ω => by rw [integral_neg]; exact neg_le_neg (hs n hn ω))
    rw [integral_neg, integral_neg] at h
    exact neg_le_neg_iff.mp h
  have haux (t : ℕ) (ht : t ≤ T) :
      (∫ ω, V ω 0 ∂(Measure.infinitePi fun _ : ℕ => μ)) ≤
        ∫ ω, V ω t ∂(Measure.infinitePi fun _ : ℕ => μ) := by
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact (ih (by omega)).trans (hstep t (by omega))
  exact haux T le_rfl
end Parking
