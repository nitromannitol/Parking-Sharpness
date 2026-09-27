import Mathlib
import Parking.MainTheorems
import ParkingAudit.Support.ParkingVocabulary
import ParkingAudit.Support.Bridge

/-!
# Solution: Trichotomy

The challenge module `ParkingAudit/Trichotomy/Challenge.lean` imports only Mathlib and states the
theorem with one intentional `sorry`. This solution imports the repository together with
`ParkingAudit.Support.ParkingVocabulary`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `Parking.trichotomy` through the bridges in
`ParkingAudit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is
not definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.trichotomy`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.4 (`thm:trichotomy`). -/
theorem trichotomy (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
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
  revert hGrowth hBernstein d hd
  rw [Bridge.meanU_eq, Bridge.meanu_eq, Bridge.U_eq, Bridge.uOf_eq, Bridge.criticalLaw_eq,
    Bridge.sandpileGrowth_eq, Bridge.bernstein_eq]
  exact Parking.trichotomy

end ParkingAudit
