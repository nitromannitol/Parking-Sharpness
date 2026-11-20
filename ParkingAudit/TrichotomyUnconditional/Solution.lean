import Mathlib
import Parking.Unconditional.Trichotomy
import ParkingAudit.Support.TrichotomyBridge

/-!
# Solution: TrichotomyUnconditional

The challenge module `ParkingAudit/TrichotomyUnconditional/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`. This solution proves the byte-identical statement
from `Parking.trichotomy_proved`. It reuses the vocabulary and the bridge lemmas of the `Trichotomy`
pair (`ParkingAudit/Trichotomy/SolutionBasic.lean` and
`ParkingAudit/Support/TrichotomyBridge.lean`), whose vocabulary block is byte-identical to this
pair's `SolutionBasic.lean`: the statement is reverted, every vocabulary constant that is not
definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.trichotomy_proved`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.4 (`thm:trichotomy`). -/
theorem trichotomy_unconditional
    (d : ℕ) (hd : 1 ≤ d) :
    (d ≤ 3 → ∀ (ν : Measure ℤ), CriticalLaw ν →
      (∀ᵐ ω ∂(law d ν),
        Tendsto (fun n : ℕ => ((U ω n 0 : ℝ) - uOf ω n 0) /
          meanu (law d ν) n) atTop (𝓝 0)) ∧
      (∀ r : ℝ, 1 ≤ r →
        (∀ n : ℕ, Integrable (fun ω => |((U ω n 0 : ℝ) - uOf ω n 0) /
          meanu (law d ν) n| ^ r) (law d ν)) ∧
        Tendsto (fun n : ℕ => ∫ ω, |((U ω n 0 : ℝ) - uOf ω n 0) /
          meanu (law d ν) n| ^ r ∂(law d ν)) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => meanU (law d ν) n /
        meanu (law d ν) n) atTop (𝓝 1) ∧
      ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ =>
        (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * meanU (law d ν) n) atTop (𝓝 L)) ∧
    (d = 4 → (∀ (ν : Measure ℤ), CriticalLaw ν →
      (∀ n : ℕ, 1 ≤ n → 1 ≤ meanU (law d ν) n / meanu (law d ν) n) ∧
      ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
        meanU (law d ν) n / meanu (law d ν) n ≤ B) ∧
      ∀ B : ℝ, 0 < B → ∃ ν : Measure ℤ, CriticalLaw ν ∧
        B ≤ liminf (fun n : ℕ => meanU (law d ν) n /
          meanu (law d ν) n) atTop) ∧
    (5 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν → (∃ b : ℤ, ν (Set.Iio b) = 0) →
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * Real.log n ∧
        c * Real.log n ≤ ∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν) ∧
          ∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν) ≤ C * Real.log n) ∧
      Tendsto (fun n : ℕ => meanU (law d ν) n /
        meanu (law d ν) n) atTop atTop) := by
  revert d hd
  rw [Bridge.meanU_eq, Bridge.meanu_eq, Bridge.U_eq, Bridge.uOf_eq, Bridge.criticalLaw_eq]
  exact Parking.trichotomy_proved

end ParkingAudit
