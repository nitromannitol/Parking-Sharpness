import Parking.Support.SpaceTimeSceneryCoupling
import Parking.External.SpatialOdometerScalingOfDSP

/-!
# Spatial odometer scaling

The spatial odometer scaling limit follows from the continuum stopping stability of the
divisible sandpile and the space-time coupling with retained scenery for integer critical laws.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The spatial odometer scaling limit, given the continuum stopping stability of the divisible
sandpile. -/
theorem Parking.External.spatialOdometerScaling_of_dsp
    (hStab : Sandpile.External.ContinuumStoppingStability.{0}) :
    Parking.External.SpatialOdometerScaling
-- FROZEN-STATEMENT-END
:= Parking.External.spatialOdometerScaling_of_coupling Parking.Support.spaceTimeCouplingCritical
  hStab
