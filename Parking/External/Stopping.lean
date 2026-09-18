/-
The optimal stopping representation of the divisible sandpile odometer, which
`parking.tex` quotes at `parking.tex:866-874` (label `lem:stopping`) from
Bou-Rabee, Panagiotis, Rossignol and Sun, Theorem 3.2 there, multiplied by `2d`
to match the normalization used here.

It was assumed.  It is now proved in the shared library, on a general graph and
then on the lattice, and `Parking.External.stopping` discharges it, so every
node that carries it as a hypothesis can be given the theorem.

A stopping time bounded by `n` for the natural filtration of the walk is
`LatticeProb.IsWalkStopping`: whether it takes the value `k` is settled by the
positions up to time `k`.  The reward `∑_{j<σ} η(X_j)` is
`LatticeProb.Graph.Zd.sceneryPartialSum`, and `E_x` is the integral against
`LatticeProb.siteWalkLaw d x`, the law of the walk from `x`.  The supremum is
asserted as a least upper bound, so that no junk value of an unattained or
unbounded supremum can satisfy it.
-/
import Parking.Support.Walk
import LatticeProb.Graph.ZdRepresentation

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "Let $X$ be the simple random walk.  For every configuration
$\eta\in\mathbb R^{\Z^d}$, every $n\geq0$ and $x\in\Z^d$,
$u_n(x)=\sup_{\sigma\leq n}\E_x\sum_{j=0}^{\sigma-1}\eta(X_j)$, where the
supremum is over stopping times for the natural filtration of $X$, bounded by
$n$ and including $\sigma=0$; the stopping rule may depend on $\eta$." -/
def Parking.External.Stopping : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (η : Parking.Site d → ℝ) (n : ℕ) (x : Parking.Site d),
    IsLUB (LatticeProb.Graph.Zd.zdStopValues η n x) (Parking.u η n x)
-- FROZEN-STATEMENT-END

/-- The divisible odometer of `Parking.Basic` is the one the library's
representation is stated for; both are the same recursion. -/
theorem Parking.u_eq_zdOdometer {d : ℕ} (η : Parking.Site d → ℝ) (n : ℕ) :
    Parking.u η n = LatticeProb.Graph.Zd.zdOdometer η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      show max 0 (η x + LatticeProb.walkOp (Parking.u η n) x)
        = max 0 (η x + LatticeProb.walkOp (LatticeProb.Graph.Zd.zdOdometer η n) x)
      rw [ih]

/-- The quoted representation, proved in the shared library. -/
theorem Parking.External.stopping : Parking.External.Stopping := by
  intro d hd η n x
  rw [show Parking.u η n x = LatticeProb.Graph.Zd.zdOdometer η n x from
    congrFun (Parking.u_eq_zdOdometer η n) x]
  exact LatticeProb.Graph.Zd.parkingStopping' d hd η n x
