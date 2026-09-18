/-
Homogeneity of the discrete optimal-stopping value: scaling the terminal reward by a
nonnegative constant scales the value by the same constant.  This is the missing step in
`Parking.uOriented_eq_potential_add_stoppingSup`'s own Dynkin decomposition needed to turn
the RESCALED odometer `n^{-1/4} u⃗_n(0)` into a value of a RESCALED terminal-reward problem,
which is exactly the form `Parking.orientedCutoffValue`'s own terminal reward already has.

The underlying fact (`sSup`/`BddAbove` under a nonnegative-scalar image) is generic and lives
in `Parking.Generic.OptimalStopping`; this file only instantiates it at `Parking.
orientedTerminalValues`/`Parking.orientedStoppingSup`.
-/
import Parking.Support.OrientedTerminal
import Parking.Generic.OptimalStopping

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- **The value of the terminal-reward stopping problem is homogeneous of degree `1` in the
reward, for a nonnegative scalar.** -/
theorem orientedStoppingSup_const_mul {c : ℝ} (hc : 0 ≤ c) (F : ℕ → Site d → ℝ) (n : ℕ)
    (x : Site d) :
    orientedStoppingSup d (fun k y => c * F k y) n x = c * orientedStoppingSup d F n x := by
  unfold orientedStoppingSup
  rw [orientedTerminalValues_const_mul]
  exact Generic.OptimalStopping.sSup_const_mul_image_of_nonneg (orientedTerminalValues d F n x) hc

/-- **`BddAbove` of the terminal values of a nonnegatively-scaled reward.** -/
theorem bddAbove_orientedTerminalValues_const_mul {c : ℝ} (hc : 0 ≤ c) (F : ℕ → Site d → ℝ)
    (n : ℕ) (x : Site d) (hS : BddAbove (orientedTerminalValues d F n x)) :
    BddAbove (orientedTerminalValues d (fun k y => c * F k y) n x) := by
  rw [orientedTerminalValues_const_mul]
  exact Generic.OptimalStopping.bddAbove_const_mul_image_of_nonneg hS hc

end Parking

end
