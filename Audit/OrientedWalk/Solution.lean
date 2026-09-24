import Mathlib
import Parking.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: OrientedWalk

The challenge module `Audit/OrientedWalk/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.oriented_walk` through the bridges in
`Audit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is not
definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.oriented_walk`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.8 (`thm:oriented-walk`). -/
theorem oriented_walk (hBern : External.Bernstein)
    (hConc : External.UConcentration)
    (hStability : External.OrientedStoppingStability)
    (hBinomial : External.BinomialLocalCLT)
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
        meanuOriented (orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => S (orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) := by
  revert hBern hConc hStability hBinomial d hd ν hν
  rw [Bridge.meanuOriented_eq, Bridge.meanU_eq, Bridge.S_eq, Bridge.criticalLaw_eq,
    Bridge.bernstein_eq, Bridge.uConcentration_eq, Bridge.orientedStoppingStability_eq,
    Bridge.binomialLocalCLT_eq]
  exact Parking.oriented_walk

end ParkingAudit
