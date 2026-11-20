import Parking.MainTheorems
import Parking.External.BernsteinProved
import Parking.External.SandpileGrowthUnconditional

/-!
# Corollary 1.3 without hypotheses

Corollary 1.3 (`cor:growth`) holds with no cited hypothesis: the growth of the mean
divisible sandpile odometer is `Parking.External.sandpileGrowth_holds` and the martingale
Bernstein estimate is `Parking.External.bernstein`.
-/

open MeasureTheory

/-- **Corollary 1.3** (`cor:growth`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.growth_proved
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
      (∀ t : ℕ,
        c * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) ≤ Parking.S (Parking.law d ν) t ∧
          Parking.S (Parking.law d ν) t ≤ C * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)))) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * Real.log n) ∧
      (∀ t : ℕ,
        c / ((t : ℝ) + 1) ≤ Parking.S (Parking.law d ν) t ∧
          Parking.S (Parking.law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1)))
-- FROZEN-STATEMENT-END
:=
  Parking.growth Parking.External.sandpileGrowth_holds Parking.External.bernstein d hd ν hν
