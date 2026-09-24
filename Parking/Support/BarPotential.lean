/-
`Parking.barPotential`: the FIRST summand of the Dynkin decomposition
(`Parking.u_eq_potential_add_stoppingSup`, `Parking/Support/Terminal.lean`) of the rescaled
divisible odometer `Parking.barDivisible`, at the SAME rescaling convention
(`R^{d/2-2}·V_{⌊sR²⌋}(⌊Rx⌋)`, matching `barDivisible`'s `R^{d/2-2}·u_{⌊sR²⌋}(⌊Rx⌋)` with `u`
replaced by the linear potential `V = linPotential`). Its point-evaluation convergence is what
Step 1 of the proof of `prop:spatial-scaling` needs for this summand.
-/
import Parking.Support.Continuum
import Parking.Support.Terminal
import Parking.Support.UConcBridge

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **`R^{d/2-2}·V_{⌊sR²⌋}(⌊Rx⌋)`**, the linear-potential summand of `Parking.barDivisible`
under the Dynkin decomposition `Parking.u_eq_potential_add_stoppingSup`. -/
def barPotential {d : ℕ} (η : Site d → ℝ) (R : ℝ) (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  R ^ ((d : ℝ) / 2 - 2) * linPotential η ⌊s * R ^ 2⌋₊ (latticePoint R x)

/-- **`barDivisible` splits as `barPotential` plus the rescaled stopping-value summand.** -/
theorem barDivisible_eq_barPotential_add (hd : 1 ≤ d) (ω : Data d) (R s : ℝ) (x : Fin d → ℝ) :
    barDivisible ω R s x = barPotential (confReal ω) R s x
      + R ^ ((d : ℝ) / 2 - 2) *
        stoppingSup d (fun k y => -linPotential (confReal ω) (⌊s * R ^ 2⌋₊ - k) y)
          ⌊s * R ^ 2⌋₊ (latticePoint R x) := by
  unfold barDivisible barPotential
  rw [uOf_eq_u_confReal, u_eq_potential_add_stoppingSup hd, mul_add]

end Parking

end
