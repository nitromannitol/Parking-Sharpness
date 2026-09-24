/-
Theorem 1.6 of parking.tex, frozen.  `parking.tex:289-302`
(label `thm:nearest-counterexample`):

  "For every $d\geq5$, there exist $p_d\in(0,1/2)$ and $c>0$ such that, if
   $\eta$ is i.i.d. with $\P(\eta(0)=1)=\P(\eta(0)=-1)=p_d$ and
   $\P(\eta(0)=0)=1-2p_d$, then
   $\liminf_t\P(\text{the origin is closer to an unfilled hole than to an active
   particle at time }t)\geq c$."

Distances are graph distances from the origin, in `ℕ∞`, as
`parking.tex:588-601` fixes them; the proof of this theorem uses the `l^1`
identity $|w_i-a_i|=|w_i-y_i|+|a_i-y_i|$ and `l^1` balls.
The cited martingale inequality enters through the one-point and two-hole
estimates as an explicit hypothesis.
-/
import Parking.Support.ThreePointLaw
import Parking.Support.NearestCounterexampleProof

open MeasureTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.nearest_counterexample (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((Parking.law d (Parking.threePointLaw p)) {ω | Parking.HoleCloser ω t}).toReal) atTop
-- FROZEN-STATEMENT-END
:= by
  exact Parking.nearest_counterexample_proof hBernstein d hd
