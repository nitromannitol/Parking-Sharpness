/-
A telescoping sum over `ℕ` for an arbitrary real sequence. No object of this repository's
model enters the statement: `f : ℕ → ℝ` is arbitrary.

It is used in `signedM`'s martingale bound (`Parking/Support/SpatWMartingaleVariance.lean`) to
telescope `∑_{k<t} (meanU(k+1) - meanU(k))` down to `meanU(t) - meanU(0)`.
-/
import Mathlib

noncomputable section
namespace Parking.Generic.Telescope

/-- **A telescoping sum over `ℕ`.** `∑_{k<t} (f(k+1) - f(k)) = f(t) - f(0)`, for an arbitrary
real sequence `f`. -/
theorem sum_range_sub_telescope (f : ℕ → ℝ) (t : ℕ) :
    ∑ k ∈ Finset.range t, (f (k + 1) - f k) = f t - f 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ, ih]; ring

end Parking.Generic.Telescope
end
