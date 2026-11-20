import Parking.MainTheorems
import Parking.External.BernsteinProved
import Parking.External.MultivariateBerryEsseenProved
import Parking.External.SandpileGrowthUnconditional
import Parking.External.SpatialOdometerScalingUnconditional

/-!
# Theorem 1.5 without hypotheses

Theorem 1.5 (`thm:nearest`) holds with no cited hypothesis: the growth of the mean
divisible sandpile odometer is `Parking.External.sandpileGrowth_holds`, the martingale
Bernstein estimate is `Parking.External.bernstein`, the spatial odometer scaling limit is
`Parking.External.spatialOdometerScaling_holds`, the two heat equation inputs are
`Parking.External.heatInteriorRegularity` and `Parking.External.heatCompactness`, and the
multivariate Berry–Esseen comparison is `Parking.External.multivariateBerryEsseen`.
-/

open MeasureTheory Filter Topology

/-- **Theorem 1.5** (`thm:nearest`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.nearest_proved
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:=
  Parking.nearest Parking.External.sandpileGrowth_holds Parking.External.bernstein
    Parking.External.spatialOdometerScaling_holds Parking.External.heatInteriorRegularity
    Parking.External.heatCompactness Parking.External.multivariateBerryEsseen d hd hd3 ν hν
