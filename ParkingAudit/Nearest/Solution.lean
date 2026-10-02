import Mathlib
import Parking.MainTheorems
import ParkingAudit.Nearest.SolutionBasic
import ParkingAudit.Support.NearestBridge

/-!
# Solution: Nearest

The challenge module `ParkingAudit/Nearest/Challenge.lean` imports only Mathlib and states the
theorem with one intentional `sorry`. This solution imports the repository together with
`ParkingAudit.Nearest.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Parking.nearest` through the bridge lemmas in
`ParkingAudit/Support/NearestBridge.lean`: the statement is reverted, every vocabulary constant that
is not definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.nearest`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.5 (`thm:nearest`). -/
theorem nearest (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hOdometer : External.SpatialOdometerScaling)
    (hInterior : External.HeatInteriorRegularity)
    (hCompact : External.HeatCompactness)
    (hBerry : External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal)
      atTop (𝓝 0) := by
  revert hGrowth hBernstein hOdometer hInterior hCompact
    hBerry d hd hd3 ν hν
  rw [Bridge.criticalLaw_eq, Bridge.HoleCloser_eq, Bridge.sandpileGrowth_eq, Bridge.bernstein_eq,
    Bridge.spatialOdometerScaling_eq,
    Bridge.heatInteriorRegularity_eq, Bridge.heatCompactness_eq,
    Bridge.multivariateBerryEsseen_eq]
  exact Parking.nearest

end ParkingAudit
