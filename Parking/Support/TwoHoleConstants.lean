import Parking.Support.LogFromTail

noncomputable section
namespace Parking

/-- The finite-box factor and fourth-power tail have the claimed two-hole form, with one uniform constant. -/
theorem exists_two_hole_constant_assembly (Cb Cs Ci A : ℝ)
    (hCb : 0 < Cb) (hCs : 0 < Cs) (hCi : 0 < Ci) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ h b P : ℝ, 0 < h → h ≤ 1 / 4 → 0 ≤ b →
      P ≤ Real.exp (Ci * (A * (1 + Real.log (1 / h)) * (Cb * b))) *
        (Real.exp (Cs * (Cb * b)) * h ^ 2) + h ^ 4 →
      P ≤ C * h ^ 2 * Real.exp (C * Real.log (1 / h) * b) := by
  let L0 := Real.log 4
  have hL0 : 0 < L0 := Real.log_pos (by norm_num)
  let K := Cb * (Ci * A + (Ci * A + Cs) / L0)
  let C := max 2 K
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, fun h b P hh hh4 hb hP => ?_⟩
  let L := Real.log (1 / h)
  have hL : L0 ≤ L := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    apply (le_div_iff₀ hh).mpr
    linarith
  have hLpos : 0 < L := hL0.trans_le hL
  have hratio : 0 ≤ (Ci * A + Cs) / L0 := by positivity
  have hsmall := mul_le_mul_of_nonneg_left hL hratio
  rw [div_mul_cancel₀ _ hL0.ne'] at hsmall
  have hscalar : Ci * A * (1 + L) + Cs ≤ (Ci * A + (Ci * A + Cs) / L0) * L := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hscalar (mul_nonneg hCb.le hb)
  have hK : Ci * (A * (1 + L) * (Cb * b)) + Cs * (Cb * b) ≤ K * L * b := by
    dsimp only [K]
    nlinarith only [hscale]
  have hExp : Ci * (A * (1 + L) * (Cb * b)) + Cs * (Cb * b) ≤ C * L * b :=
    hK.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 2 K) hLpos.le) hb)
  have hh1 : h ≤ 1 := hh4.trans (by norm_num)
  have hsq : h ^ 2 ≤ 1 := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have hfour : h ^ 4 ≤ h ^ 2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hsq)]
  have he1 : 1 ≤ Real.exp (C * L * b) := Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg hC.le hLpos.le) hb)
  have htail : h ^ 4 ≤ h ^ 2 * Real.exp (C * L * b) :=
    hfour.trans (by nlinarith [mul_le_mul_of_nonneg_left he1 (sq_nonneg h)])
  calc
    P ≤ Real.exp (Ci * (A * (1 + L) * (Cb * b))) * (Real.exp (Cs * (Cb * b)) * h ^ 2) + h ^ 4 := hP
    _ = h ^ 2 * Real.exp (Ci * (A * (1 + L) * (Cb * b)) + Cs * (Cb * b)) + h ^ 4 := by rw [Real.exp_add]; ring
    _ ≤ h ^ 2 * Real.exp (C * L * b) + h ^ 2 * Real.exp (C * L * b) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (sq_nonneg h)) htail
    _ = 2 * h ^ 2 * Real.exp (C * L * b) := by ring
    _ ≤ C * h ^ 2 * Real.exp (C * L * b) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left 2 K) (sq_nonneg h)) (Real.exp_pos _).le
end Parking
