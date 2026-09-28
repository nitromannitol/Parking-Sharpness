import Parking.Support.OrientedNorm

/-!
# A lower bound for the directed Green norm

The first layer gives a nonzero directed Green norm at every positive horizon.
-/

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- For any horizon `n ≥ 1`, the sum `∑' x, orientedGreen d n x ^ 2` is at least `1`,
because rewriting via `tsum_orientedGreen_sq` and bounding the layer-sum below by its
`l = 0` term reduces this to the fact that `orientedLayer d 0` is the point mass at `0`. -/
theorem one_le_orientedGreen_sq (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ∑' x : Site d, orientedGreen d n x ^ 2 := by
  rw [tsum_orientedGreen_sq]
  have h := single_le_sum (f := fun l : ℕ => ∑' x : Site d, orientedLayer d l x ^ 2)
    (fun l _ => tsum_nonneg fun x => sq_nonneg _) (mem_range.mpr (show 0 < n by omega))
  simpa [orientedLayer] using h

/-- The `l2Norm` of the truncated Green function `orientedGreen d n` is at least `1` for
`n ≥ 1`, obtained by taking square roots in `one_le_orientedGreen_sq`. -/
theorem one_le_orientedGreen_l2 (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ l2Norm (orientedGreen d n) := by
  have h := Real.sqrt_le_sqrt (one_le_orientedGreen_sq (d := d) n hn)
  simpa only [Real.sqrt_one, l2Norm, sq_abs] using h

end Parking
