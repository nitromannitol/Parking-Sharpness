/- Two-sided square-norm estimates from the binomial recurrence. -/
import Parking.Support.Shift
import LatticeProb.Walk.Series

noncomputable section
namespace Parking
open Finset

theorem conv_scaled_sq_mono : Monotone fun n : ℕ => (n : ℝ) * conv n 0 ^ 2 := by
  apply monotone_nat_of_le_succ
  intro n
  have hsq : (2 * ((n : ℝ) + 1)) ^ 2 * conv (n + 1) 0 ^ 2 =
      (2 * (n : ℝ) + 1) ^ 2 * conv n 0 ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) (conv_zero_succ n)
    simpa only [mul_pow] using h
  push_cast
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 4 * ((n : ℝ) + 1))
  calc (n : ℝ) * conv n 0 ^ 2 * (4 * ((n : ℝ) + 1))
      ≤ (2 * (n : ℝ) + 1) ^ 2 * conv n 0 ^ 2 := by
        nlinarith [sq_nonneg (conv n 0)]
    _ = ((n : ℝ) + 1) * conv (n + 1) 0 ^ 2 * (4 * ((n : ℝ) + 1)) := by
        rw [← hsq]
        ring

theorem conv_zero_sq_lower (n : ℕ) : (1 / 4 : ℝ) ≤ ((n : ℝ) + 1) * conv n 0 ^ 2 := by
  by_cases hn : n = 0
  · norm_num [hn, conv_zero_index]
  · have h := conv_scaled_sq_mono (show 1 ≤ n by omega)
    have he : conv 1 0 = (1 / 2 : ℝ) := by norm_num [conv_zero_eq, Nat.centralBinom]
    norm_num [he] at h
    nlinarith [sq_nonneg (conv n 0)]

theorem conv_zero_upper (n : ℕ) : conv n 0 ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
  have hpos : 0 < Real.sqrt ((n : ℝ) + 1) := by positivity
  apply (le_div_iff₀ hpos).mpr
  have he : (conv n 0 * Real.sqrt ((n : ℝ) + 1)) ^ 2 = ((n : ℝ) + 1) * conv n 0 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  nlinarith [conv_zero_sq_le n]

theorem conv_zero_lower (n : ℕ) : (1 / 2 : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤ conv n 0 := by
  have hpos : 0 < Real.sqrt ((n : ℝ) + 1) := by positivity
  apply (div_le_iff₀ hpos).mpr
  have he : (conv n 0 * Real.sqrt ((n : ℝ) + 1)) ^ 2 = ((n : ℝ) + 1) * conv n 0 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hn := mul_nonneg (conv_nonneg n 0) hpos.le
  nlinarith [conv_zero_sq_lower n]

theorem sum_conv_zero_upper (n : ℕ) :
    (∑ l ∈ range n, conv l 0) ≤ 2 * Real.sqrt n := by
  exact (sum_le_sum fun l _ => conv_zero_upper l).trans (LatticeProb.sum_inv_sqrt_le n)

theorem sum_conv_zero_lower (n : ℕ) :
    (1 / 2 : ℝ) * Real.sqrt n ≤ ∑ l ∈ range n, conv l 0 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hb : ∀ l ∈ range n, (1 / 2 : ℝ) / Real.sqrt n ≤ conv l 0 := by
    intro l hl
    refine le_trans ?_ (conv_zero_lower l)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show l + 1 ≤ n by have := mem_range.mp hl; omega)
  have hsum := sum_le_sum hb
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  have he : (n : ℝ) * ((1 / 2 : ℝ) / Real.sqrt n) = (1 / 2 : ℝ) * Real.sqrt n := by
    rw [← mul_div_assoc, div_eq_iff hs.ne']
    nlinarith [Real.sq_sqrt hn0.le]
  rwa [he] at hsum

end Parking
