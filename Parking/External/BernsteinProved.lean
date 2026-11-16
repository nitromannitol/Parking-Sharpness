import Parking.External.Bernstein
import LatticeProb.Prob.BernsteinJoint

/-!
# Martingale Bernstein inequalities

The two Bernstein moment estimates hold with a common universal constant.
-/

/-- The martingale Bernstein input follows from the joint moment estimates. -/
theorem Parking.External.bernstein : Parking.External.Bernstein :=
  LatticeProb.bernstein_moment_estimates
