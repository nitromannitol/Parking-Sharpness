/-
A general finite-range translation-invariant transition kernel on `Z^d`, the
recursion it drives, and its truncated Green function.  These are the objects
of `lem:u-concentration` (`parking.tex:1402-1413`), which the paper states for
an arbitrary such kernel and applies to the simple random walk kernel `P` and,
in Section 10, to the oriented kernel.

`IsLatticeKernel r K` says that `K` is nonnegative, supported within sup-distance
`r`, stochastic, and invariant under the translations of the lattice.
`kOp`, `kIter`, `kGreen` and `kSol` are `(Kf)(x)`, `K^j(0,\cdot)`,
`g^K_n=\sum_{j<n}K^j(0,\cdot)` and the solution of `v_0=0`,
`v_{n+1}=(\eta+Kv_n)^+`.  These, with `l2Norm` and `supAbs`, are defined in the
library (`LatticeProb/Walk/LatticeKernel.lean`); the names the frozen statements
use are exported into `Parking`.
-/
import Parking.Support.Walk
import LatticeProb.Walk.LatticeKernel

noncomputable section

namespace Parking

open LatticeProb

export LatticeProb.Walk (IsLatticeKernel kGreen kSol l2Norm supAbs)

/-- `max_x g_n(x)` for the simple random walk. -/
def greenMax (d : ℕ) (n : ℕ) : ℝ := ⨆ x : Site d, green d n x

end Parking

end
