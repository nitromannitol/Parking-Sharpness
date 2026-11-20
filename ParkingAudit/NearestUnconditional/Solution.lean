import Mathlib
import Parking.Unconditional.Nearest
import ParkingAudit.Support.NearestBridge

/-!
# Solution: NearestUnconditional

The challenge module `ParkingAudit/NearestUnconditional/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`. This solution proves the byte-identical statement
from `Parking.nearest_proved`. It reuses the vocabulary and the bridge lemmas of the `Nearest` pair
(`ParkingAudit/Nearest/SolutionBasic.lean` and `ParkingAudit/Support/NearestBridge.lean`), whose
vocabulary block is byte-identical to this pair's `SolutionBasic.lean`: the statement is reverted,
every vocabulary constant that is not definitionally its counterpart is rewritten to the
repository's, and the result is closed by `Parking.nearest_proved`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.5 (`thm:nearest`). -/
theorem nearest_unconditional
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal)
      atTop (𝓝 0) := by
  revert d hd hd3 ν hν
  rw [Bridge.criticalLaw_eq, Bridge.HoleCloser_eq]
  exact Parking.nearest_proved

end ParkingAudit
