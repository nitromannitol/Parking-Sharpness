import Parking.MainTheorems
import Parking.External.BernsteinProved
import Parking.External.SandpileGrowthUnconditional

/-!
# Theorem 1.7 without hypotheses

Theorem 1.7 (`thm:near`) holds with no cited hypothesis: the growth of the mean divisible
sandpile odometer is `Parking.External.sandpileGrowth_holds`, the martingale Bernstein
estimate is `Parking.External.bernstein`, and the optimal stopping representation of the
divisible odometer is `Parking.External.stopping`.
-/

open MeasureTheory
open scoped ENNReal

/-- **Theorem 1.7** (`thm:near`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.near_proved
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
      ENNReal.ofReal (c * Parking.nearRate d δ) ≤ Parking.meanUlimit (Parking.law d (ν δ)) ∧
        Parking.meanUlimit (Parking.law d (ν δ)) ≤ ENNReal.ofReal (C * Parking.nearRate d δ)
-- FROZEN-STATEMENT-END
:=
  Parking.near Parking.External.sandpileGrowth_holds Parking.External.bernstein d hd δ₀ hδ₀ ν
    hprob hmean hnonconst θ M hθ hexp K hcouple
