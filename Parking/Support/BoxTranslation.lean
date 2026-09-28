import Parking.Support.OrthantCube

/-!
# Translation and symmetry of the box membership relation

The lattice box `boxFinset y R` is invariant under a simultaneous translation of its center
and the tested point, and membership in it is symmetric in the center and the point.
-/

namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Translating both the center and the tested point by the same vector does not change
membership in `boxFinset`. -/
theorem mem_boxFinset_translate (v y w : Site d) (R : ℕ) :
    w + v ∈ boxFinset (y + v) R ↔ w ∈ boxFinset y R := by
  simp only [mem_boxFinset_iff, Pi.add_apply, add_sub_add_right_eq_sub]

/-- Membership in `boxFinset` is symmetric in the center and the tested point. -/
theorem mem_boxFinset_symm {y w : Site d} {R : ℕ} :
    w ∈ boxFinset y R ↔ y ∈ boxFinset w R := by
  simp only [mem_boxFinset_iff, abs_sub_comm]

end Parking
