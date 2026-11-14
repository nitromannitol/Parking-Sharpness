import Parking.External.SandpileGrowthProved
import Sandpile.External.LocalCLTProved

/-!
# Sandpile growth from the two continuum inputs

`Parking.External.sandpileGrowth` derives `Parking.External.SandpileGrowth` from three
Divisible-Sandpile-Percolation inputs: the local central limit theorem
`Sandpile.External.LocalCLT`, the continuum stopping stability
`Sandpile.External.ContinuumStoppingStability` and the continuum optimal stopping
`Sandpile.External.ContinuumOptimalStopping`.  Divisible-Sandpile-Percolation proves the first
of them (`Sandpile.External.localCLT`), so the growth statement follows from the two continuum
inputs alone.
-/

/-- `Parking.External.SandpileGrowth` from the continuum stopping stability and the continuum
optimal stopping of Divisible-Sandpile-Percolation; the local central limit theorem is
`Sandpile.External.localCLT`. -/
theorem Parking.External.sandpileGrowth_of_dsp
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB],
      Sandpile.External.ContinuumOptimalStopping ΩB) :
    Parking.External.SandpileGrowth :=
  Parking.External.sandpileGrowth Sandpile.External.localCLT hStab hOS
