import Mathlib
import Parking.Unconditional.Master
import ParkingAudit.Support.MasterBridge

/-!
# Solution: MasterUnconditional

The challenge module `ParkingAudit/MasterUnconditional/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`. This solution proves the byte-identical statement
from `Parking.master_proved`. It reuses the vocabulary and the bridge lemmas of the `Master` pair
(`ParkingAudit/Master/SolutionBasic.lean` and `ParkingAudit/Support/MasterBridge.lean`), whose
vocabulary block is byte-identical to this pair's `SolutionBasic.lean`: the statement is reverted,
every vocabulary constant that is not definitionally its counterpart is rewritten to the
repository's, and the result is closed by `Parking.master_proved`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.2 (`thm:master`). -/
theorem master_unconditional
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (meanu (law d ν) n + Real.log n) ≤ meanU (law d ν) n ∧
        meanU (law d ν) n ≤ C * (meanu (law d ν) n + Real.log n) := by
  revert d hd ν hprob hnonconst hmean θ hθ hexp
  rw [Bridge.meanU_eq, Bridge.meanu_eq]
  exact Parking.master_proved

end ParkingAudit
