import Mathlib
import Parking.MainTheorems
import ParkingAudit.Growth.SolutionBasic
import ParkingAudit.Support.GrowthBridge

/-!
# Solution: Growth

The challenge module `ParkingAudit/Growth/Challenge.lean` imports only Mathlib and states the
theorem with one intentional `sorry`. This solution imports the repository together with
`ParkingAudit.Growth.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.growth` through the bridge lemmas in
`ParkingAudit/Support/GrowthBridge.lean`: the statement is reverted, every vocabulary constant that
is not definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.growth`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Corollary 1.3 (`cor:growth`). -/
theorem growth (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
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
  revert hGrowth hBernstein d hd ν hν
  rw [Bridge.meanU_eq, Bridge.S_eq, Bridge.criticalLaw_eq, Bridge.sandpileGrowth_eq,
    Bridge.bernstein_eq]
  exact Parking.growth

end ParkingAudit
