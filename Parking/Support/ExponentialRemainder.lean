/- A global quadratic remainder bound for the real exponential. -/
import Mathlib.Analysis.Complex.Exponential

namespace Parking

theorem exp_quadratic_remainder (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  have h0 : ‖(Real.exp x : ℂ) - (1 + (x : ℂ))‖ ≤ x ^ 2 * Real.exp |x| := by
    simpa [Finset.sum_range_succ, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs] using h
  have he : (Real.exp x : ℂ) - (1 + (x : ℂ)) = ((Real.exp x - (1 + x) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he] at h0
  have h' : |Real.exp x - (1 + x)| ≤ x ^ 2 * Real.exp |x| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h0
  linarith [le_abs_self (Real.exp x - (1 + x))]

end Parking
