import Mathlib
import Parking.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: Nearest

The challenge module `Audit/Nearest/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.nearest` through the bridges in
`Audit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is not
definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.nearest`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.5 (`thm:nearest`). -/
theorem nearest (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration)
    (hGreenNorms : External.GreenNorms)
    (hOdometer : External.SpatialOdometerScaling)
    (hInterior : External.HeatInteriorRegularity)
    (hMinimum : External.HeatStrongMinimum)
    (hCompact : External.HeatCompactness)
    (hLower : External.CriticalScaleLowerTail)
    (hVar : External.VarianceScale)
    (hBerry : External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal)
      atTop (𝓝 0) := by
  revert hGrowth hBernstein hConcentration hGreenNorms hOdometer hInterior hMinimum hCompact hLower
    hVar hBerry d hd hd3 ν hν
  rw [Bridge.criticalLaw_eq, Bridge.HoleCloser_eq, Bridge.sandpileGrowth_eq, Bridge.bernstein_eq,
    Bridge.uConcentration_eq, Bridge.greenNorms_eq, Bridge.spatialOdometerScaling_eq,
    Bridge.heatInteriorRegularity_eq, Bridge.heatStrongMinimum_eq, Bridge.heatCompactness_eq,
    Bridge.criticalScaleLowerTail_eq, Bridge.varianceScale_eq, Bridge.multivariateBerryEsseen_eq]
  exact Parking.nearest

end ParkingAudit
