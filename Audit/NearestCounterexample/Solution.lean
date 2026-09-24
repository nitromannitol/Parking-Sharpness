import Mathlib
import Parking.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: NearestCounterexample

The challenge module `Audit/NearestCounterexample/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.nearest_counterexample` through the bridges in
`Audit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is not
definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.nearest_counterexample`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.6 (`thm:nearest-counterexample`). -/
theorem nearest_counterexample (hBernstein : External.Bernstein) (d : ℕ)
    (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal) atTop := by
  revert hBernstein d hd
  rw [Bridge.HoleCloser_eq, Bridge.bernstein_eq]
  exact Parking.nearest_counterexample

end ParkingAudit
