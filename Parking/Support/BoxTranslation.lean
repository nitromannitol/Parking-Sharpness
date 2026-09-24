import Parking.Support.OrthantCube

namespace Parking
open LatticeProb
variable {d : ℕ}

theorem mem_boxFinset_translate (v y w : Site d) (R : ℕ) :
    w + v ∈ boxFinset (y + v) R ↔ w ∈ boxFinset y R := by
  simp only [mem_boxFinset_iff, Pi.add_apply, add_sub_add_right_eq_sub]

theorem mem_boxFinset_symm {y w : Site d} {R : ℕ} :
    w ∈ boxFinset y R ↔ y ∈ boxFinset w R := by
  simp only [mem_boxFinset_iff, abs_sub_comm]

end Parking
