/-
**The optimal-stopping value's spatial increment is controlled by the reward's own spatial
modulus, uniformly over the relevant time range.**

The bound is a Lipschitz-in-reward transfer, and it avoids building a Kolmogorov process for
the reflected odometer `u` directly, which is a nonlinear object. The Dynkin decomposition
`u = V + stoppingSup(-V·)` (`Parking.u_eq_potential_add_stoppingSup`,
`Parking/Support/Terminal.lean`) writes the odometer as the POTENTIAL plus an optimal-stopping
value whose reward, at a FIXED time-shape, is read at the walk's OWN current site translated by
the starting site `x` (`Parking.Support.StoppingShift.stoppingSup_eq_shift`). So the SPATIAL
increment of the stopping value between two starting sites `x` and `x'` is bounded by the SAME
reward's own spatial modulus, taken over the whole relevant time range `k ≤ n` and over every
site the walk can reach, in ONE application of the reward's `1`-Lipschitz-ness
(`Parking.abs_stoppingSup_sub_le_of_le`, the `k ≤ n`-restricted form) — no regularity of
`u`/`stoppingSup` itself as a STOCHASTIC PROCESS is proved or needed; only the DETERMINISTIC
reward's own modulus is.

Feeding the horizon-UNIFORM space-direction bound that `Parking.Support.SpatGreenShift` proves
for the linear field `V` through this transfer gives `u`'s spatial equicontinuity, WITHOUT ever
building a Kolmogorov-Chentsov process for `u` directly.

The statement mentions no object specific to the parking data (no `Parking.Data`, `Parking.law`,
`linHatInterp`, `scenePair`, `signedPair`, or the odometer `U`): it is stated for an abstract
reward `F : ℕ → Site d → ℝ` and the shared walk/stopping machinery (`Parking.stoppingSup`,
`Parking.Site`), which is developed in `Parking.Support` (`Terminal.lean`, `StoppingShift.lean`,
`ValueLipschitz.lean`).
-/
import Parking.Support.ValueLipschitz
import Parking.Support.StoppingShift

noncomputable section

namespace Parking.Generic.StoppingModulus

open Parking

variable {d : ℕ}

/-- **The value's spatial increment is bounded by the reward's own spatial modulus, uniform
over the relevant time range `k ≤ n`.** The Dynkin-decomposition transfer lemma: no
regularity of `u`/`stoppingSup` as a process is used, only the DETERMINISTIC reward `F`'s own
modulus of spatial continuity, read at every reachable site simultaneously (not merely along
one fixed path). -/
theorem abs_stoppingSup_sub_le_of_spatial_modulus (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ)
    (x x' : Site d) {M c : ℝ} (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M)
    (hmod : ∀ k ≤ n, ∀ y : Site d, |F k (x + y) - F k (x' + y)| ≤ c) :
    |Parking.stoppingSup d F n x - Parking.stoppingSup d F n x'| ≤ c := by
  rw [Parking.stoppingSup_eq_shift F n x, Parking.stoppingSup_eq_shift F n x']
  exact Parking.abs_stoppingSup_sub_le_of_le hd (fun k y => F k (x + y))
    (fun k y => F k (x' + y)) n (0 : Site d) (fun k y => hbound k (x + y))
    (fun k y => hbound k (x' + y)) hmod

/-- **Corollary, at a fixed CONSTANT modulus bound uniform over `k`.** The common special
case where the reward's spatial modulus does not depend on the time coordinate at all
(e.g. a cutoff-truncated version of a jointly continuous field, whose own modulus is a
single number on a compact time-space box). -/
theorem abs_stoppingSup_sub_le_of_spatial_modulus_const (hd : 1 ≤ d) (F : ℕ → Site d → ℝ)
    (n : ℕ) (x x' : Site d) {M c : ℝ} (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M)
    (hmod : ∀ y : Site d, ∀ k, |F k (x + y) - F k (x' + y)| ≤ c) :
    |Parking.stoppingSup d F n x - Parking.stoppingSup d F n x'| ≤ c :=
  abs_stoppingSup_sub_le_of_spatial_modulus hd F n x x' hbound (fun k _hk y => hmod y k)

end Parking.Generic.StoppingModulus

end
