/- The geometric factor in finite dyadic chaining. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace Parking

def dyadicFactor (A b : ℝ) : ℕ → ℝ
  | 0 => 1
  | L + 1 => A * dyadicFactor A b L + b ^ (L + 1)

theorem dyadicFactor_nonneg {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (L : ℕ) :
    0 ≤ dyadicFactor A b L := by
  induction L with
  | zero => exact zero_le_one
  | succ L ih => exact add_nonneg (mul_nonneg hA ih) (pow_nonneg hb _)

theorem dyadicFactor_identity (A b : ℝ) (L : ℕ) :
    dyadicFactor A b L * (A - b) = A ^ (L + 1) - b ^ (L + 1) := by
  induction L with
  | zero => simp [dyadicFactor]
  | succ L ih =>
    rw [dyadicFactor, add_mul, mul_assoc, ih, pow_succ A (L + 1), pow_succ b (L + 1)]
    ring

theorem dyadicFactor_le {A b : ℝ} (hb : 0 ≤ b) (h : b < A) (L : ℕ) :
    dyadicFactor A b L ≤ (A / (A - b)) * A ^ L := by
  apply (le_div_iff₀ (sub_pos.mpr h)).mpr
    (show dyadicFactor A b L * (A - b) ≤ A * A ^ L by
      rw [dyadicFactor_identity, pow_succ]
      nlinarith [pow_nonneg hb (L + 1)]) |>.trans_eq
  ring

end Parking
