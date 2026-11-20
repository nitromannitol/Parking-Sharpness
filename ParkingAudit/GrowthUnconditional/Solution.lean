import Mathlib
import Parking.Unconditional.Growth
import ParkingAudit.Support.GrowthBridge

/-!
# Solution: GrowthUnconditional

The challenge module `ParkingAudit/GrowthUnconditional/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`. This solution proves the byte-identical statement
from `Parking.growth_proved`. It reuses the vocabulary and the bridge lemmas of the `Growth` pair
(`ParkingAudit/Growth/SolutionBasic.lean` and `ParkingAudit/Support/GrowthBridge.lean`), whose
vocabulary block is byte-identical to this pair's `SolutionBasic.lean`: the statement is reverted,
every vocabulary constant that is not definitionally its counterpart is rewritten to the
repository's, and the result is closed by `Parking.growth_proved`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Corollary 1.3 (`cor:growth`). -/
theorem growth_unconditional
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
      (∀ t : ℕ,
        c * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) ≤ S (law d ν) t ∧
          S (law d ν) t ≤ C * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)))) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * Real.log n) ∧
      (∀ t : ℕ,
        c / ((t : ℝ) + 1) ≤ S (law d ν) t ∧
          S (law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1))) := by
  revert d hd ν hν
  rw [Bridge.meanU_eq, Bridge.S_eq, Bridge.criticalLaw_eq]
  exact Parking.growth_proved

end ParkingAudit
