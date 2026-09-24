/- An exponentially decreasing increment bound forces logarithmic growth. -/
import Mathlib

noncomputable section
namespace Parking

theorem log_one_add_mul_lower {b : ℝ} (hb : 0 < b) (n : ℕ) :
    min 1 b * Real.log ((n : ℝ) + 1) ≤ Real.log (1 + b * n) := by
  let p : ℝ := min 1 b
  have hp : 0 < p := lt_min zero_lt_one hb
  have hple : p ≤ 1 := min_le_left _ _
  have hpble : p ≤ b := min_le_right _ _
  have hpow := rpow_one_add_le_one_add_mul_self
    (show (-1 : ℝ) ≤ n by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hp.le hple
  have hbnd : (1 + (n : ℝ)) ^ p ≤ 1 + b * n := by
    have := mul_le_mul_of_nonneg_right hpble (Nat.cast_nonneg n)
    linarith
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (by positivity) p) hbnd
  rw [Real.log_rpow (by positivity)] at hlog
  simpa only [add_comm (1 : ℝ) (n : ℝ), p] using hlog

theorem logarithmic_growth_of_exp_increment (a : ℕ → ℝ) (ha0 : a 0 = 0)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hstep : ∀ n, c * Real.exp (-L * a n) ≤ a (n + 1) - a n) :
    ∃ k : ℝ, 0 < k ∧ ∀ n : ℕ, k * Real.log ((n : ℝ) + 1) ≤ a n := by
  have hinc (n : ℕ) : c * L ≤ Real.exp (L * a (n + 1)) - Real.exp (L * a n) := by
    have he := Real.add_one_le_exp (L * (a (n + 1) - a n))
    have h1 := mul_le_mul_of_nonneg_left he (Real.exp_pos (L * a n)).le
    have h2 := mul_le_mul_of_nonneg_left (hstep n) (mul_pos (Real.exp_pos (L * a n)) hL).le
    have hprod : Real.exp (L * a n) * Real.exp (L * (a (n + 1) - a n)) =
        Real.exp (L * a (n + 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcancel : Real.exp (L * a n) * Real.exp (-L * a n) = 1 := by
      rw [← Real.exp_add, show L * a n + -L * a n = 0 by ring, Real.exp_zero]
    rw [hprod] at h1
    have h2left : Real.exp (L * a n) * L * (c * Real.exp (-L * a n)) = c * L := by
      calc
        _ = c * L * (Real.exp (L * a n) * Real.exp (-L * a n)) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rw [h2left] at h2
    nlinarith
  have hbound (n : ℕ) : 1 + (c * L) * n ≤ Real.exp (L * a n) := by
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      have hs := hinc n
      push_cast
      nlinarith
  refine ⟨min 1 (c * L) / L, div_pos (lt_min zero_lt_one (mul_pos hc hL)) hL, fun n => ?_⟩
  have hlog := Real.log_le_log (show (0 : ℝ) < 1 + (c * L) * n by positivity) (hbound n)
  rw [Real.log_exp] at hlog
  have hlo := (log_one_add_mul_lower (mul_pos hc hL) n).trans hlog
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hL).mpr (by nlinarith [hlo])

end Parking
