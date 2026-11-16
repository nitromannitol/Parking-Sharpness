import Parking.MainTheorems
import Parking.External.BernsteinProved

/-!
# The master theorem with the Bernstein estimate

The critical comparison holds with the martingale Bernstein estimate supplied by the library.
-/

open MeasureTheory

/-- The critical comparison with the Bernstein estimate supplied. -/
theorem Parking.master_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (Parking.meanu (Parking.law d ν) n + Real.log n) ≤ Parking.meanU (Parking.law d ν) n ∧
        Parking.meanU (Parking.law d ν) n ≤
            C * (Parking.meanu (Parking.law d ν) n + Real.log n) :=
  Parking.master hGrowth Parking.External.bernstein d hd ν hprob hnonconst hmean θ hθ hexp
