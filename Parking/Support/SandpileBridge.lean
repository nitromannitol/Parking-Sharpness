import Parking.External.SandpileGrowth
import Sandpile.Support.SceneryBridge

/-!
# Bridge to the divisible-sandpile odometer

Bridge between Parking's real-field odometer and the divisible-sandpile
formalization.

Parking writes the centred field directly and uses `walkOp`; the sandpile
development writes a mass field `σ`, converts it to the scenery
`(σ - 1) / (2d)`, and uses `avg`.  The recursions are the same after this
conversion.  The law identity below is the corresponding normalization
`σ = 1 + 2dζ`, and transports the sandpile mean from the centred mass law to
Parking's i.i.d. scenery law.
-/

open MeasureTheory ProbabilityTheory

namespace Parking

variable {d : ℕ}

/-- The zero step of Parking's odometer. -/
theorem u_zero (η : Site d → ℝ) : Parking.u η 0 = 0 := by
  rfl

/-- The successor step of Parking's odometer. -/
theorem u_succ (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    Parking.u η (n + 1) x = max 0 (η x + LatticeProb.walkOp (Parking.u η n) x) := by
  rfl

/-- The Parking and sandpile odometer recursions agree pointwise. -/
theorem u_eq_sandpile_odometerOf (η : Site d → ℝ) (n : ℕ) :
    Parking.u η n = Sandpile.odometerOf η n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      funext x
      rw [u_succ, Sandpile.odometerOf]
      unfold Sandpile.avg
      rw [ih]

/-- The mean of Parking's odometer is the mean of the sandpile odometer in
the scenery language. -/
theorem meanSandpileReal_eq_sceneryMean (d : ℕ) (ν : Measure ℝ) (n : ℕ) :
    Parking.External.meanSandpileReal d ν n =
      ∫ ζ, Sandpile.odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
  unfold Parking.External.meanSandpileReal
  exact integral_congr_ae (Filter.Eventually.of_forall fun η =>
    congrFun (u_eq_sandpile_odometerOf η n) 0)

/-- The mean sandpile observable under the centred mass law equals Parking's
mean sandpile observable under the i.i.d. scenery law. -/
theorem meanSandpileReal_eq_sandpileMean (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 1 ≤ d) (n : ℕ) :
    Parking.External.meanSandpileReal d ν n =
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n := by
  rw [meanSandpileReal_eq_sceneryMean d ν n,
    (Sandpile.meanOdometer_centeredMassLaw_eq d ν hd n).symm]

end Parking
