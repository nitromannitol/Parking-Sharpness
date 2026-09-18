/-
Young's inequality in the shape the directed Step 2 of `thm:oriented-walk`
(`parking.tex:3282-3294`) uses: the square-root term of the directed
`prop:w-moment` is absorbed into the left-hand side, leaving
`X ≤ 2Y + a² + 2a` from `X ≤ Y + a(√X + 1)`.
-/
import Parking.Support.UpperStep

noncomputable section

namespace Parking

open MeasureTheory

/-- **Young's absorption with the constant term.**  If `X ≤ Y + a(√X + 1)` with
`X ≥ 0`, then `X ≤ 2Y + a² + 2a`. -/
theorem young_absorb_sqrt_one {X Y a : ℝ} (hX : 0 ≤ X)
    (h : X ≤ Y + a * (Real.sqrt X + 1)) : X ≤ 2 * Y + a ^ 2 + 2 * a := by
  have hX2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have hkey : 2 * (a * Real.sqrt X) ≤ a ^ 2 + X := by
    nlinarith [sq_nonneg (a - Real.sqrt X), Real.sqrt_nonneg X]
  nlinarith

end Parking

end

/-- The absorption of Step 2 of `thm:oriented-walk` at `d = 2`: from
`X ≤ C n^{1/4} + C n^{1/8}(√X + 1)` with everything nonnegative follows
`X ≤ (2C + C² + 2C) n^{1/4}`. -/
theorem oriented_two_absorb {X C : ℝ} {n : ℕ} (hX : 0 ≤ X) (hC : 0 ≤ C) (hn : 1 ≤ n)
    (h : X ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) + C * (n : ℝ) ^ ((1 : ℝ) / 8) * (Real.sqrt X + 1)) :
    X ≤ (2 * C + C ^ 2 + 2 * C) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h4 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have h8 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos (by linarith) _
  have h84 : (n : ℝ) ^ ((1 : ℝ) / 8) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hkey : X ≤ 2 * (C * (n : ℝ) ^ ((1 : ℝ) / 4)) + (C * (n : ℝ) ^ ((1 : ℝ) / 8)) ^ 2
      + 2 * (C * (n : ℝ) ^ ((1 : ℝ) / 8)) :=
    Parking.young_absorb_sqrt_one hX h
  have hsq : (C * (n : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = C ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 8)) 2,
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ (n:ℝ))]
    norm_num
  rw [hsq] at hkey
  nlinarith [h84, hC, h4, h8]

/-- The `X^{1/16}` term of the directed Step 2 moment inequality is `√X` in
disguise: `X^{1/16} = (X^{1/8})^{1/2}` for `X ≥ 0`. -/
theorem rpow_sixteenth_eq_sqrt_eighth {X : ℝ} (hX : 0 ≤ X) :
    X ^ ((1 : ℝ) / 16) = Real.sqrt (X ^ ((1 : ℝ) / 8)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX]
  norm_num

/-- The absorption of Step 4 of `thm:oriented-walk` (`parking.tex:3336-3344`):
from `X ≤ C L + C (√(r X) + r)` with `X ≥ 0`, `C ≥ 0`, `L ≥ 1`, `2 ≤ r` and
`r ≤ 2 L`, the moment bound `X ≤ C' L` follows. -/
theorem oriented_log_absorb {X C L r : ℝ} (hX : 0 ≤ X) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hr : 2 ≤ r) (hrL : r ≤ 2 * L)
    (h : X ≤ C * L + C * (Real.sqrt (r * X) + r)) :
    X ≤ (4 * C + 4 * C ^ 2 + 4 * C) * L := by
  have hr0 : 0 ≤ r := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hsr : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsqr : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0
  have hsqX : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
  have hmul : Real.sqrt r * Real.sqrt X = Real.sqrt (r * X) := by
    rw [mul_comm r X, Real.sqrt_mul hX r, mul_comm]
  have h1 : 2 * (C * Real.sqrt (r * X)) ≤ C ^ 2 * r + X := by
    nlinarith [sq_nonneg (C * Real.sqrt r - Real.sqrt X), hsqr, hsqX, hmul, hC, hsr, hsX]
  have h4 : C * r ≤ C * (2 * L) := mul_le_mul_of_nonneg_left hrL hC
  nlinarith [h, h1, h4, hC, hL0, hr0, hX]
