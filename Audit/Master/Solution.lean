import Mathlib
import Parking.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: Master

The challenge module `Audit/Master/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.master` through the bridges in
`Audit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is not
definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.master`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.2 (`thm:master`). -/
theorem master (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration)
    (hGreenNorms : External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (meanu (law d ν) n + Real.log n) ≤ meanU (law d ν) n ∧
        meanU (law d ν) n ≤ C * (meanu (law d ν) n + Real.log n) := by
  revert hGrowth hBernstein hConcentration hGreenNorms d hd ν hprob hnonconst hmean θ hθ hexp
  rw [Bridge.meanU_eq, Bridge.meanu_eq, Bridge.sandpileGrowth_eq, Bridge.bernstein_eq,
    Bridge.uConcentration_eq, Bridge.greenNorms_eq]
  exact Parking.master

end ParkingAudit
