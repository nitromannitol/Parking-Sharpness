/-
The Brownian optimal-stopping value at a general reward.

`LatticeProb.ContinuumStopping.contStopValue` is the value `sup_{τ≤T} E_0[-Z_T(τ,B_τ)]` of
`parking.tex:3201-3205` at the particular reward `-Z_T`.  The cited stability
estimates are about a general bounded reward, so the same value is recorded here
for an arbitrary `G : ℝ → ℝ → ℝ`, with the elapsed time as its first argument,
and `LatticeProb.ContinuumStopping.contStopValue` is read off as the special case
`G s y = -Z_T(s,y)(ω)`.

As everywhere in the repository, a stopping time of the Brownian motion is
recorded by Galmarino's criterion (`LatticeProb.ContinuumStopping.IsContStopping`), and the value is
an `sSup` over the reals attained by the admissible rules; the rule that stops
at once is admissible, so the set is never empty.

These objects are defined in the library (`LatticeProb/ContinuumStoppingValue.lean`,
namespace `LatticeProb.ContinuumStopping`); `contValue`, which a frozen statement names, is
exported into `Parking`.
-/
import LatticeProb.ContinuumStoppingBounds
import Parking.Support.ContOrientedLimit
import LatticeProb.ContinuumStoppingValue

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

export LatticeProb.ContinuumStopping (contValue)

end Parking

end
