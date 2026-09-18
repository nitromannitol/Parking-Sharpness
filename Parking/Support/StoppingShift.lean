/-
**The discrete optimal-stopping value at a general starting site reduces to the value
at the origin, of the reward shifted by that site.**

`Parking.walkPath` is driven by a sequence of signed directions read off the SAME law
`Parking.walkLaw d` whatever the starting site, and one step's displacement
(`Parking.stepVec`) does not depend on the current position, so the whole path from `x` is
the path from the origin, translated by `x`.  This is what lets
`Parking.External.SpatialStoppingStability` (stated only for the walk started at the origin,
matching the convention `Parking.ofBrownianSpace`/`LatticeProb.IsBrownianSpace d 0 B PB` fixes
for the Brownian motion) be applied to `Parking.stoppingSup` at an arbitrary starting site `x`,
needed by `Parking.u_eq_potential_add_stoppingSup` (`Parking/Support/Terminal.lean`), which is
stated for general `x`.
-/
import Parking.Support.Terminal

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The walk from `x` is the walk from the origin, translated by `x`.**  Immediate
induction on the step count from `Parking.walkPath`'s own recursion, since one step's
displacement does not depend on the current position. -/
theorem walkPath_eq_add_walkPath_zero (x : Site d) (p : ℕ → Fin d × Bool) (j : ℕ) :
    walkPath x p j = x + walkPath (0 : Site d) p j := by
  induction j with
  | zero => simp [walkPath]
  | succ j ih => rw [walkPath, ih, walkPath, add_assoc]

/-- **The expected terminal reward at a general starting site is the expected terminal
reward at the origin, of the reward shifted by that site.**  Pointwise equality of the
integrands, from `walkPath_eq_add_walkPath_zero`. -/
theorem terminalValue_eq_shift (F : ℕ → Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) :
    terminalValue F x σ = terminalValue (fun k y => F k (x + y)) (0 : Site d) σ := by
  unfold terminalValue
  congr 1
  funext p
  rw [walkPath_eq_add_walkPath_zero x p (σ p)]

/-- **The set of terminal values at a general starting site is exactly the set of terminal
values at the origin, of the shifted reward.**  Both sides quantify over the same stopping
rules (`IsStoppingTimeLE` does not depend on the starting site), so the two sets of
attainable values coincide by `terminalValue_eq_shift`. -/
theorem terminalValues_eq_shift (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    terminalValues d F n x = terminalValues d (fun k y => F k (x + y)) n (0 : Site d) := by
  ext a
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, terminalValue_eq_shift F x σ⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, (terminalValue_eq_shift F x σ).symm⟩

/-- **The discrete optimal-stopping value at a general starting site `x` equals the value
at the origin, of the reward shifted by `x`.**  This is what makes
`Parking.External.SpatialStoppingStability` (fixed at the origin) applicable to
`Parking.u_eq_potential_add_stoppingSup` at any site. -/
theorem stoppingSup_eq_shift (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    stoppingSup d F n x = stoppingSup d (fun k y => F k (x + y)) n (0 : Site d) := by
  unfold stoppingSup
  rw [terminalValues_eq_shift F n x]

end Parking

end
