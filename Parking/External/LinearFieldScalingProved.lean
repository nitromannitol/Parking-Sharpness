import Parking.Support.SandpileContinuousGreen
import Parking.Support.LinearFieldFdd
import Parking.Support.SceneryCovarianceLimit
import Parking.Support.LinearFieldScalingOfFdd

/-!
# Linear field scaling

The joint scaling limit of the interpolated linear field and the scenery follows from the
finite-dimensional convergence and the continuous Green field construction.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The scaling limit of the linear field and the scenery. -/
theorem Parking.External.linearFieldScaling_holds : Parking.External.LinearFieldScaling
-- FROZEN-STATEMENT-END
:= Parking.Support.linearFieldScaling_of_fdd Parking.exists_continuous_green_field
  Parking.Support.linHatInterpBridge
  (Parking.Support.jointLinearFdd_of_sceneryCovarianceLimit Parking.sceneryCovarianceLimit)
