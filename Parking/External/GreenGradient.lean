/-
External input: the gradient of the truncated Green function of the simple
random walk in dimension two and above (`parking.tex:1019-1030`, label
`eq:green-gradient`), which the paper obtains from the first-difference local
central limit estimate and the Gaussian bound of Lawler-Limic, Section 2.3.

Stated for `2 ≤ d` only.  In dimension one the gradient is computed exactly
inside the proof of `lem:gamma-sum`, in `Parking/Support/GammaSum.lean`, so
nothing is assumed there.  The `Prop` enters only as an explicit hypothesis of
the results whose proofs use it, and `lem:gamma-sum` carries it that way.

It is no longer an assumption.  The shared library proves the bound for the
truncated Green function of the simple walk, uniformly in the truncation time,
which is the form the sum of `lem:gamma-sum` needs, and
`Parking.External.greenGradient` below discharges the `Prop` against it.  The
route is the lazy walk, whose truncated Green function at horizon `2m` is the
simple walk's at horizon `m` smoothed by the binomial profile; the parity
constraint of the simple walk is what makes the transfer, rather than the lazy
bound itself, the statement to prove.

The constant depends only on the dimension, so it is bound before the
truncation time and before the sites.
-/
import Parking.Support.GreenBridge
import LatticeProb.Walk.SRWGreenGrad

-- FROZEN-STATEMENT-BEGIN
/-- "For every $m\geq1$, every $y$, and every neighbor $z$ of $y$,
$|g_m(y)-g_m(z)|\leq C(1+|y|)^{1-d}$."  Here `|y|` is the graph distance
from the origin, as `parking.tex:588-601` fixes distances on the lattice. -/
def Parking.External.GreenGradient (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ y z : Parking.Site d,
    z ∈ LatticeProb.nbrFinset y →
      |Parking.green d m y - Parking.green d m z|
        ≤ C * (1 + (Parking.graphNorm y : ℝ)) ^ (1 - (d : ℝ))
-- FROZEN-STATEMENT-END

/-- The quoted bound, proved in the shared library for the truncated Green
function of the simple walk, uniformly in the truncation. -/
theorem Parking.External.greenGradient (d : ℕ) (hd : 2 ≤ d) :
    Parking.External.GreenGradient d := by
  obtain ⟨C, hC, hgrad⟩ := LatticeProb.exists_srwGreen_gradient d hd
  refine ⟨C, hC, ?_⟩
  intro m _ y z hz
  rw [Parking.green_eq_srwGreen, Parking.green_eq_srwGreen]
  exact hgrad m y z hz
