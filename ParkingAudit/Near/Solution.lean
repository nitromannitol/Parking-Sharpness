import Mathlib
import Parking.MainTheorems
import ParkingAudit.Support.ParkingVocabulary
import ParkingAudit.Support.Bridge

/-!
# Solution: Near

The challenge module `ParkingAudit/Near/Challenge.lean` imports only Mathlib and states the
theorem with one intentional `sorry`. This solution imports the repository together with
`ParkingAudit.Support.ParkingVocabulary`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `Parking.near` through the bridges in
`ParkingAudit/Support/Bridge.lean`: the statement is reverted, every vocabulary constant that is
not definitionally its counterpart is rewritten to the repository's, and the result is closed by
`Parking.near`.
-/

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.7 (`thm:near`). -/
theorem near (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (ν : ℝ → Measure ℤ)
    (hprob : ∀ δ ∈ Set.Icc 0 δ₀, IsProbabilityMeasure (ν δ))
    (hmean : ∀ δ ∈ Set.Icc 0 δ₀, ∫ k, (k : ℝ) ∂(ν δ) = -δ)
    (hnonconst : ∀ k : ℤ, ν 0 {k} ≠ 1)
    (θ M : ℝ) (hθ : 0 < θ)
    (hexp : ∀ δ ∈ Set.Icc 0 δ₀, Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) ∧
      ∫ k, Real.exp (θ * |(k : ℝ)|) ∂(ν δ) ≤ M)
    (K : ℝ) (hcouple : ∀ δ ∈ Set.Ioc 0 δ₀, ∃ π : Measure (ℤ × ℤ), IsProbabilityMeasure π ∧
      π.map Prod.fst = ν δ ∧ π.map Prod.snd = ν 0 ∧
      ∫ p, |((p.1 : ℝ) - p.2)| ∂π ≤ K * δ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Set.Ioc 0 δ₁,
      ENNReal.ofReal (c * nearRate d δ) ≤ meanUlimit (law d (ν δ)) ∧
        meanUlimit (law d (ν δ)) ≤ ENNReal.ofReal (C * nearRate d δ) := by
  revert hGrowth hBernstein d hd δ₀ hδ₀ ν hprob hmean hnonconst θ M hθ hexp K
    hcouple
  rw [Bridge.meanUlimit_eq, Bridge.sandpileGrowth_eq,
    Bridge.bernstein_eq]
  exact Parking.near

end ParkingAudit
