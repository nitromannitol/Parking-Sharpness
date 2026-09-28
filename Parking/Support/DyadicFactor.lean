import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The dyadic chaining factor

The geometric factor accumulated by finite dyadic chaining: `dyadicFactor A b L` obeys the
recursion `dyadicFactor A b 0 = 1`, `dyadicFactor A b (L+1) = A * dyadicFactor A b L + b ^
(L+1)`, the constant produced when a chaining bound with growth rate `A` and per-level cost `b`
is unrolled over `L` levels. `dyadicFactor_identity` gives it in closed form through a
telescoping identity, and `dyadicFactor_le` bounds it by `(A / (A - b)) * A ^ L` when `b < A`.
-/

noncomputable section
namespace Parking

/-- The dyadic chaining constant: `dyadicFactor A b 0 = 1` and `dyadicFactor A b (L+1) = A *
dyadicFactor A b L + b ^ (L+1)`. -/
def dyadicFactor (A b : ℝ) : ℕ → ℝ
  | 0 => 1
  | L + 1 => A * dyadicFactor A b L + b ^ (L + 1)

/-- `dyadicFactor A b L` is nonnegative when `A` and `b` are, by induction on `L`. -/
theorem dyadicFactor_nonneg {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (L : ℕ) :
    0 ≤ dyadicFactor A b L := by
  induction L with
  | zero => exact zero_le_one
  | succ L ih => exact add_nonneg (mul_nonneg hA ih) (pow_nonneg hb _)

/-- The telescoping identity `dyadicFactor A b L * (A - b) = A ^ (L+1) - b ^ (L+1)`, proved by
induction on `L`. -/
theorem dyadicFactor_identity (A b : ℝ) (L : ℕ) :
    dyadicFactor A b L * (A - b) = A ^ (L + 1) - b ^ (L + 1) := by
  induction L with
  | zero => simp [dyadicFactor]
  | succ L ih =>
    rw [dyadicFactor, add_mul, mul_assoc, ih, pow_succ A (L + 1), pow_succ b (L + 1)]
    ring

/-- `dyadicFactor A b L ≤ (A / (A - b)) * A ^ L` when `0 ≤ b < A`, via `dyadicFactor_identity`
and dropping the nonpositive term `-b ^ (L+1)`. -/
theorem dyadicFactor_le {A b : ℝ} (hb : 0 ≤ b) (h : b < A) (L : ℕ) :
    dyadicFactor A b L ≤ (A / (A - b)) * A ^ L := by
  apply (le_div_iff₀ (sub_pos.mpr h)).mpr
    (show dyadicFactor A b L * (A - b) ≤ A * A ^ L by
      rw [dyadicFactor_identity, pow_succ]
      nlinarith [pow_nonneg hb (L + 1)]) |>.trans_eq
  ring

end Parking
