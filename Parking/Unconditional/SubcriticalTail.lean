import Parking.Basic
import Parking.Support.RangeUpperScaling

/-!
# Theorem 1.1 without hypotheses

Theorem 1.1 (`thm:subcritical-tail`) holds with no cited hypothesis: the two-sided
stretched-exponential bounds for the range of the walk proved in
`Parking/Support/RangeUpperScaling.lean` replace the Donsker–Varadhan limit
`Parking.External.DonskerVaradhanRange` carried by `Parking.Frozen.subcritical_tail`.
-/

open MeasureTheory

/-- **Theorem 1.1** (`thm:subcritical-tail`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.subcritical_tail_proved
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ Parking.S (Parking.law d ν) t ∧
        Parking.S (Parking.law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2))))
-- FROZEN-STATEMENT-END
:=
  Parking.subcritical_tail_of_range_count d hd ν hprob hint hmean hpos θ hθ hexp
