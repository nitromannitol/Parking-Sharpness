import Parking.Support.Continuum

/-!
# Spatial rescaling exponent bound

For `d ≤ 3`, the parabolic rescaling exponent `d/2 - 2` is at most `-1/2`, so the
rescaling factor `R^{d/2-2}` is dominated by `R^{-1/2}` for `R ≥ 1`. This is the
elementary monotonicity-of-`rpow` step feeding the spatial scaling estimates.
-/

namespace Parking
open MeasureTheory LatticeProb

/-- For `d ≤ 3` and `R ≥ 1`, the rescaling factor `R^{d/2-2}` is at most
`R^{-1/2}`. -/
theorem rpow_le_inv_sqrt {d : ℕ} (hd3 : d ≤ 3) {R : ℝ} (hR : 1 ≤ R) :
    R ^ ((d : ℝ) / 2 - 2) ≤ R ^ (-(1 : ℝ) / 2) := by
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hd : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  linarith

end Parking