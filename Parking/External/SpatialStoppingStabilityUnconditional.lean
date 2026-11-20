import Parking.External.SpatialStoppingStabilityOfDSP
import Sandpile.External.ContinuumStoppingStabilityProved

/-!
# The spatial stopping stability input without hypotheses

`Parking.External.SpatialStoppingStability` holds with no hypothesis: it follows from the
continuum stopping stability of the divisible sandpile
(`Parking.External.spatialStoppingStability_of_continuumStoppingStability`), which the divisible
sandpile formalization proves as `Sandpile.External.continuumStoppingStability_holds`.
-/

/-- The spatial stopping stability (`parking.tex:1756-1767`), with no hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.spatialStoppingStability_holds :
    Parking.External.SpatialStoppingStability
-- FROZEN-STATEMENT-END
:=
  Parking.External.spatialStoppingStability_of_continuumStoppingStability
    Sandpile.External.continuumStoppingStability_holds
