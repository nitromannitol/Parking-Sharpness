import Parking.External.SpatialOdometerScalingProved
import Sandpile.External.ContinuumStoppingStabilityProved

/-!
# The spatial odometer scaling input without hypotheses

`Parking.External.SpatialOdometerScaling` holds with no hypothesis: it follows from the
continuum stopping stability of the divisible sandpile
(`Parking.External.spatialOdometerScaling_of_dsp`), which the divisible sandpile formalization
proves as `Sandpile.External.continuumStoppingStability_holds`.
-/

/-- The spatial odometer scaling limit (`parking.tex:1756-1767`), with no hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.spatialOdometerScaling_holds :
    Parking.External.SpatialOdometerScaling
-- FROZEN-STATEMENT-END
:=
  Parking.External.spatialOdometerScaling_of_dsp Sandpile.External.continuumStoppingStability_holds
