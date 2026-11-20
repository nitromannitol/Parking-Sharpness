import Parking.MainTheorems
import Parking.External.BernsteinProved
import Parking.External.SandpileGrowthUnconditional

/-!
# Theorem 1.4 without hypotheses

Theorem 1.4 (`thm:trichotomy`) holds with no cited hypothesis: the growth of the mean
divisible sandpile odometer is `Parking.External.sandpileGrowth_holds`, the martingale
Bernstein estimate is `Parking.External.bernstein`, and the optimal stopping
representation of the divisible odometer is `Parking.External.stopping`.
-/

open MeasureTheory Filter Topology

/-- **Theorem 1.4** (`thm:trichotomy`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.trichotomy_proved
    (d : ℕ) (hd : 1 ≤ d) :
    (d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ᵐ ω ∂(Parking.law d ν),
        Tendsto (fun n : ℕ => ((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n) atTop (𝓝 0)) ∧
      (∀ r : ℝ, 1 ≤ r →
        (∀ n : ℕ, Integrable (fun ω => |((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n| ^ r) (Parking.law d ν)) ∧
        Tendsto (fun n : ℕ => ∫ ω, |((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n| ^ r ∂(Parking.law d ν)) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
        Parking.meanu (Parking.law d ν) n) atTop (𝓝 1) ∧
      ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ =>
        (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.meanU (Parking.law d ν) n) atTop (𝓝 L)) ∧
    (d = 4 → (∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ n : ℕ, 1 ≤ n → 1 ≤ Parking.meanU (Parking.law d ν) n / Parking.meanu (Parking.law d ν) n) ∧
      ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
        Parking.meanU (Parking.law d ν) n / Parking.meanu (Parking.law d ν) n ≤ B) ∧
      ∀ B : ℝ, 0 < B → ∃ ν : Measure ℤ, Parking.CriticalLaw ν ∧
        B ≤ liminf (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
          Parking.meanu (Parking.law d ν) n) atTop) ∧
    (5 ≤ d → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν → (∃ b : ℤ, ν (Set.Iio b) = 0) →
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * Real.log n ∧
        c * Real.log n ≤ ∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ∂(Parking.law d ν) ∧
          ∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ∂(Parking.law d ν) ≤ C * Real.log n) ∧
      Tendsto (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
        Parking.meanu (Parking.law d ν) n) atTop atTop)
-- FROZEN-STATEMENT-END
:=
  Parking.trichotomy Parking.External.sandpileGrowth_holds Parking.External.bernstein d hd
