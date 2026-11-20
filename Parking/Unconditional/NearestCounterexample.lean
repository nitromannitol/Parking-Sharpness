import Parking.MainTheorems
import Parking.External.BernsteinProved

/-!
# Theorem 1.6 without hypotheses

Theorem 1.6 (`thm:nearest-counterexample`) holds with no cited hypothesis: the martingale
Bernstein estimate is `Parking.External.bernstein`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 1.6** (`thm:nearest-counterexample`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.nearest_counterexample_proved (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((Parking.law d (Parking.threePointLaw p)) {ω | Parking.HoleCloser ω t}).toReal) atTop
-- FROZEN-STATEMENT-END
:=
  Parking.nearest_counterexample Parking.External.bernstein d hd
