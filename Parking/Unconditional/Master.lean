import Parking.MainTheorems
import Parking.External.BernsteinProved
import Parking.External.SandpileGrowthUnconditional

/-!
# Theorem 1.2 without hypotheses

Theorem 1.2 (`thm:master`) holds with no cited hypothesis: the growth of the mean
divisible sandpile odometer is `Parking.External.sandpileGrowth_holds` and the martingale
Bernstein estimate is `Parking.External.bernstein`.
-/

open MeasureTheory ProbabilityTheory

/-- **Theorem 1.2** (`thm:master`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.master_proved
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (Parking.meanu (Parking.law d ν) n + Real.log n) ≤ Parking.meanU (Parking.law d ν) n ∧
        Parking.meanU (Parking.law d ν) n ≤ C * (Parking.meanu (Parking.law d ν) n + Real.log n)
-- FROZEN-STATEMENT-END
:=
  Parking.master Parking.External.sandpileGrowth_holds Parking.External.bernstein d hd ν hprob
    hnonconst hmean θ hθ hexp
