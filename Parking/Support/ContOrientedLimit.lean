/-
The limit random variable `U(T)` of the directed scaling limit
(`parking.tex:3190-3205`).

The paper's Step 1 reads: "Let `B` be Brownian motion with `Var(B_t) = t/4`, let
`q_t` be its transition density, and let `W` be space-time white noise on
`[0,∞) × R`, independent of `B`.  Let

  `Z_T(s,x) = sqrt(Var eta(0)) ∫_s^T ∫_R q_{r-s}(x,y) W(dr,dy)`.

Conditional on `W`, let

  `U(T) = Z_T(0,0) + sup_{τ ≤ T} E_0[-Z_T(τ, B_τ)]`,

where the supremum is over stopping times of `B` bounded by `T`, and `E_0`
averages only over `B`."

Here `W` is the white noise of Lebesgue measure on the plane, which carries the
noise of `[0,∞) × R` because every test function used is supported in the time
window `(s,T)` with `0 ≤ s`.  The supremum over stopping times is taken over the
payoffs they attain, as a supremum of reals; the set is nonempty because the
stopping time `0` is admissible.

These objects are defined in the library (`LatticeProb/ContinuumNoiseField.lean`, namespace
`LatticeProb.ContinuumStopping`); `IsQuarterBrownian`, which a frozen statement names, is
exported into `Parking`.
-/
import LatticeProb.ContinuumHeatKernel
import Parking.Support.Continuum
import LatticeProb.Gauss.WhiteNoise
import LatticeProb.Gauss.BrownianCont
import LatticeProb.ContinuumNoiseField

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

export LatticeProb.ContinuumStopping (IsQuarterBrownian)

end Parking

end
