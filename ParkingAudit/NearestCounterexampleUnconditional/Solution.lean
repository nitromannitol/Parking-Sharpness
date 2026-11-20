import Mathlib
import Parking.Unconditional.NearestCounterexample
import ParkingAudit.Support.NearestCounterexampleBridge

/-!
# Solution: NearestCounterexampleUnconditional

The challenge module `ParkingAudit/NearestCounterexampleUnconditional/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`. This solution proves the byte-identical
statement from `Parking.nearest_counterexample_proved`. It reuses the vocabulary and the bridge
lemmas of the `NearestCounterexample` pair (`ParkingAudit/NearestCounterexample/SolutionBasic.lean`
and `ParkingAudit/Support/NearestCounterexampleBridge.lean`), whose vocabulary block is
byte-identical to this pair's `SolutionBasic.lean`: the statement is reverted, every vocabulary
constant that is not definitionally its counterpart is rewritten to the repository's, and the result
is closed by `Parking.nearest_counterexample_proved`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.6 (`thm:nearest-counterexample`). -/
theorem nearest_counterexample_unconditional (d : ℕ)
    (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal) atTop := by
  revert d hd
  rw [Bridge.HoleCloser_eq]
  exact Parking.nearest_counterexample_proved

end ParkingAudit
