import Parking.External.BernsteinProved
import Parking.MainTheorems

/-!
# An application of the martingale Bernstein inequalities

The nearest-hole counterexample follows with the Bernstein moment estimates supplied.
-/

open Filter

/-- In dimension at least five, the nearest-hole probability can stay bounded away from zero. -/
theorem Parking.nearest_counterexample_of_bernstein (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((Parking.law d (Parking.threePointLaw p)) {ω | Parking.HoleCloser ω t}).toReal) atTop :=
  Parking.nearest_counterexample Parking.External.bernstein d hd
