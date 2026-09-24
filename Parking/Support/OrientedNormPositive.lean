/- The first layer gives a nonzero directed Green norm at every positive horizon. -/
import Parking.Support.OrientedNorm

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

theorem one_le_orientedGreen_sq (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ∑' x : Site d, orientedGreen d n x ^ 2 := by
  rw [tsum_orientedGreen_sq]
  have h := single_le_sum (f := fun l : ℕ => ∑' x : Site d, orientedLayer d l x ^ 2)
    (fun l _ => tsum_nonneg fun x => sq_nonneg _) (mem_range.mpr (show 0 < n by omega))
  simpa [orientedLayer] using h

theorem one_le_orientedGreen_l2 (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ l2Norm (orientedGreen d n) := by
  have h := Real.sqrt_le_sqrt (one_le_orientedGreen_sq (d := d) n hn)
  simpa only [Real.sqrt_one, l2Norm, sq_abs] using h

end Parking
