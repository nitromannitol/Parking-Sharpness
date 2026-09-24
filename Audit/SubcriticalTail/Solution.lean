import Mathlib
import Parking.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: SubcriticalTail

The challenge module `Audit/SubcriticalTail/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.subcritical_tail` through the bridges in
`Audit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is not
definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.subcritical_tail`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.1 (`thm:subcritical-tail`). -/
theorem subcritical_tail
    (hDV : External.DonskerVaradhanRange)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) := by
  revert hDV d hd ν hprob hint hmean hpos θ hθ hexp
  rw [Bridge.S_eq, Bridge.donskerVaradhan_eq]
  exact Parking.subcritical_tail

end ParkingAudit
