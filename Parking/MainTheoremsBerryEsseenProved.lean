import Parking.MainTheoremsBernsteinConsequences
import Parking.External.MultivariateBerryEsseenProved
import Parking.External.SandpileGrowthOfDSP

/-!
# The nearest-hole theorem with the Berry–Esseen estimate supplied

The multivariate Berry–Esseen comparison and the Bernstein estimate are
supplied in the nearest-hole theorem.
-/

open MeasureTheory Filter Topology

/-- The nearest-hole theorem with the Bernstein, heat-equation and
multivariate Berry–Esseen estimates supplied. -/
theorem Parking.nearest_of_proved_berry (hGrowth : Parking.External.SandpileGrowth)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) :=
  Parking.nearest_heat_of_bernstein hGrowth hOdometer Parking.External.multivariateBerryEsseen
    d hd hd3 ν hν

/-- The nearest-hole theorem from the two continuum stopping inputs of the
divisible sandpile. -/
theorem Parking.nearest_of_continuum_stopping
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB],
      Sandpile.External.ContinuumOptimalStopping ΩB)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) :=
  Parking.nearest_stability_of_bernstein (Parking.External.sandpileGrowth_of_dsp hStab hOS)
    hStab Parking.External.multivariateBerryEsseen d hd hd3 ν hν
