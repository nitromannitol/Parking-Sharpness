import Parking.Support.WMomentProof
import LatticeProb.MomentNorm

/-!
# The analytic core of Step 1 of `thm:upper`

The analytic core of Step 1 of the proof of `thm:upper`, and the `L^r` norm as a
real number.

The paper's Step 1 takes `r`-th moments in `eq:pathwise-comparison`, inserts
`prop:w-moment` and absorbs the square-root term by Young's inequality.  Three
pieces of that are independent of the parking model; the first two are in the library
(`LatticeProb/MomentNorm.lean`) and the third is here:

- `LatticeProb.MomentNorm.rNorm`, the `r`-th moment norm as a real number, with
  Minkowski's inequality for it, obtained from `MeasureTheory.eLpNorm_add_le` through a
  bridge between the two.
- `LatticeProb.MomentNorm.young_absorb`, the absorption itself: an inequality
  `X ≤ Y + a(√(bX) + k)` with everything nonnegative implies
  `X ≤ 2Y + a²b + 2ak`.
- `Parking.one_le_kappa`, the fact the paper uses to write the two error terms
  as one: `κ_d(n) ≥ 1` for `n ≥ 1`, which in dimension two is
  `log(n+2) ≥ log 3 ≥ 1`.
-/

noncomputable section

namespace Parking

open MeasureTheory
open scoped ENNReal

/-! ### Young's inequality in the form the absorption needs -/

/-! ### The Green factor is at least one -/

/-- The Green-function factor `kappa d n` is at least `1` for `n ≥ 1`: in the case
split of its definition it is either directly a power at least `1`, or bounded below
using `Real.exp_one_lt_d9`, or already equal to `1`. -/
theorem one_le_kappa (d : ℕ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ kappa d n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [kappa]
  split_ifs with h1 h2
  · exact Real.one_le_rpow hn1 (by norm_num)
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have he := Real.exp_one_lt_d9
    linarith
  · exact le_refl 1

/-! ### The `r`-th moment norm -/

variable {Ω : Type} [MeasurableSpace Ω]

end Parking

end
