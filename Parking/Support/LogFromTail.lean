import Parking.Support.MomentLowerTail

noncomputable section
namespace Parking

/-- An exponential bound on a small positive probability gives a logarithmic bound on the mean. -/
theorem exists_log_bound_of_exp {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ h m : ℝ, 0 < h → h ≤ 1 / 4 →
      h ≤ A * Real.exp (-c * m) → m ≤ C * Real.log (1 / h) := by
  let L₀ := Real.log 4
  have hL₀ : 0 < L₀ := Real.log_pos (by norm_num)
  let K := |Real.log A| / L₀
  have hK : 0 ≤ K := div_nonneg (abs_nonneg _) hL₀.le
  refine ⟨(K + 1) / c, by positivity, fun h m hh hh4 hb => ?_⟩
  have hL : L₀ ≤ Real.log (1 / h) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    apply (le_div_iff₀ hh).mpr
    linarith
  have hlog := Real.log_le_log hh hb
  rw [Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have he : Real.log (1 / h) = -Real.log h := by rw [one_div, Real.log_inv]
  have hKL := mul_le_mul_of_nonneg_left hL hK
  have hk : K * L₀ = |Real.log A| := div_mul_cancel₀ _ hL₀.ne'
  rw [hk] at hKL
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith [le_abs_self (Real.log A)]
end Parking
