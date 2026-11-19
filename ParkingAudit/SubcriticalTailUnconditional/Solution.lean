import Parking.Support.RangeUpperScaling
import ParkingAudit.Support.SubcriticalTailBridge

/-!
# Theorem 1.1 without the range limit

The range-count estimate proves the theorem in the comparator vocabulary.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.1 (`thm:subcritical-tail`). -/
theorem subcritical_tail_unconditional
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) := by
  revert d hd ν hprob hint hmean hpos θ hθ hexp
  rw [Bridge.S_eq]
  exact Parking.subcritical_tail_of_range_count

end ParkingAudit
