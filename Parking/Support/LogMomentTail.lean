import Parking.Support.MomentTail

noncomputable section
namespace Parking
open MeasureTheory

/-- Linear moments and a logarithmic mean give a fourth-power exceptional probability. -/
theorem exists_log_moment_upper_tail (C D : ℝ) (hC : 0 < C) (hD : 0 < D) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (F : Ω → ℝ) (_ : ∀ ω, 0 ≤ F ω) (h m B : ℝ),
      0 < h → h ≤ 1 → 0 < B → m ≤ D * Real.log (1 / h) →
      (∀ r : ℝ, 2 ≤ r → Integrable (fun ω => F ω ^ r) μ ∧ rNorm μ r F ≤ C * (m + r) * B) →
      (μ {ω | A * (1 + Real.log (1 / h)) * B < F ω}).toReal ≤ h ^ 4 := by
  let A := C * (D + 4) * Real.exp 1
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro Ω _ μ _ F hF h m B hh hh1 hB hm hb
  let L := Real.log (1 / h)
  have hL : 0 ≤ L := Real.log_nonneg ((le_div_iff₀ hh).mpr (by linarith))
  let r := 4 * (1 + L)
  have hr : 2 ≤ r := by dsimp only [r]; linarith
  have hr0 : 0 < r := by linarith
  let a := A * (1 + L) * B
  have ha : 0 < a := by dsimp only [a]; positivity
  have hmb : m + r ≤ (D + 4) * (1 + L) := by dsimp only [r, L] at *; nlinarith
  have hn : rNorm μ r F ≤ C * (D + 4) * (1 + L) * B :=
    (hb r hr).2.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmb hC.le) hB.le).trans_eq (by ring))
  have he : Real.exp (-1) * a = C * (D + 4) * (1 + L) * B := by
    dsimp only [a, A]
    rw [Real.exp_neg]
    field_simp
  have hratio : rNorm μ r F / a ≤ Real.exp (-1) := (div_le_iff₀ ha).mpr (by rwa [he])
  have hi : Integrable (fun ω => |F ω| ^ r) μ := by simpa only [abs_of_nonneg (hF _)] using (hb r hr).1
  have ht := measure_gt_le_rNorm_div_rpow μ F hr0 ha hi
  simp only [abs_of_nonneg (hF _)] at ht
  apply ht.trans
  apply (Real.rpow_le_rpow (div_nonneg (rNorm_nonneg _ _ _) ha.le) hratio hr0.le).trans
  rw [← Real.exp_mul]
  have heh : h ^ 4 = Real.exp (-(4 * L)) := by
    rw [show L = -Real.log h by dsimp only [L]; rw [one_div, Real.log_inv]]
    rw [show -(4 * -Real.log h) = Real.log h * (4 : ℝ) by ring, Real.exp_mul, Real.exp_log hh]
    norm_num
  rw [heh]
  apply Real.exp_le_exp.mpr
  dsimp only [r]
  linarith
end Parking
