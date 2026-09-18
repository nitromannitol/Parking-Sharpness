/-
The oriented walk of Section 10 of `parking.tex` as a path measure, and the
bounded optimal stopping problem whose value is the oriented divisible
odometer.

The odometer of `eq:oriented-divisible` (`parking.tex:3003`) is `u⃗_0 = 0`,
`u⃗_{n+1} = (η + P⃗u⃗_n)^+`, which is the dynamic programming equation of the
stopping problem with reward `∑_{j<σ} η(X_j)` along the `P⃗`-walk, exactly as
`eq:stopping` (`parking.tex:866-874`) is for the simple random walk.

The trajectory is driven by the same direction sequence as the simple random
walk of `Parking/Support/Walk.lean`, a sequence in `Fin d × Bool` with the
uniform law `walkLaw d`; the oriented step from `x` reads only the coordinate
`(p j).1` and goes to `x - e_{(p j).1}`, which is how the oriented operator is
already read in `Parking.integral_stepLaw_oriented`.  So the oriented walk needs
no new path measure, and a stopping time of the oriented walk is
`Parking.IsStoppingTimeLE`.
-/
import Parking.Support.OrientedPathMax

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The reward `∑_{j<σ} η(X_j)` collected along one oriented trajectory. -/
def orientedStopReward (η : Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) (p : ℕ → Fin d × Bool) : ℝ :=
  ∑ j ∈ Finset.range (σ p), η (orientedPath x p j)

/-- `E_x ∑_{j<σ} η(X_j)`, the expected reward of the oriented stopping rule. -/
def orientedStopValue (η : Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) : ℝ :=
  ∫ p, orientedStopReward η x σ p ∂(walkLaw d)

/-- The set of expected rewards of the oriented stopping rules bounded by `n`,
over which the oriented form of `eq:stopping` takes its supremum. -/
def orientedStopValues (d : ℕ) (η : Site d → ℝ) (n : ℕ) (x : Site d) : Set ℝ :=
  {v | ∃ σ, IsStoppingTimeLE n σ ∧ v = orientedStopValue η x σ}

/-- The position after `j` steps reads only the first `j` directions. -/
theorem orientedPath_congr (x : Site d) (j : ℕ) {p q : ℕ → Fin d × Bool}
    (h : ∀ i, i < j → p i = q i) : orientedPath x p j = orientedPath x q j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show orientedPath x p j - unit (p j).1 = orientedPath x q j - unit (q j).1
      rw [ih (fun i hi => h i (by omega)), h j (by omega)]

end Parking

end
