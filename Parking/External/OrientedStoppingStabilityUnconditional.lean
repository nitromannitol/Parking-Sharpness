import Parking.External.OrientedStoppingStabilityOfDSP
import Sandpile.External.ContinuumStoppingStabilityProved

/-!
# The oriented stopping stability input without hypotheses

`Parking.External.OrientedStoppingStability` holds with no hypothesis: it follows from the
one-dimensional case of the continuum stopping stability of the divisible sandpile
(`Parking.External.orientedStoppingStability_of_continuumStoppingStability`), which the divisible
sandpile formalization proves as `Sandpile.External.continuumStoppingStability_holds`.
-/

/-- The oriented stopping stability (`parking.tex:3214-3218`), with no hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.orientedStoppingStability_holds :
    Parking.External.OrientedStoppingStability
-- FROZEN-STATEMENT-END
:=
  Parking.External.orientedStoppingStability_of_continuumStoppingStability
    Sandpile.External.continuumStoppingStability_holds
