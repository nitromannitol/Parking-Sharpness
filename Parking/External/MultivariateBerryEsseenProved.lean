import Parking.External.MultivariateBerryEsseen
import Sandpile.External.MultivariateBerryEsseenProved

/-!
# The multivariate Berry–Esseen comparison

The orthant comparison follows from the corresponding result for the
divisible sandpile.
-/

namespace Parking.External

/-- The multivariate Berry–Esseen comparison for orthants. -/
theorem multivariateBerryEsseen : MultivariateBerryEsseen :=
  Sandpile.External.multivariateBerryEsseen_holds

end Parking.External
