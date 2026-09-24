import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace ParkingAudit.Statements

open ParkingAudit
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/SubcriticalTail/Challenge.lean`. -/
def subcritical_tail : Prop :=
  ∀ (hDV : External.DonskerVaradhanRange)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν),
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2))))

/-- The statement of `Audit/Master/Challenge.lean`. -/
def master : Prop :=
  ∀ (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration)
    (hGreenNorms : External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν),
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (meanu (law d ν) n + Real.log n) ≤ meanU (law d ν) n ∧
        meanU (law d ν) n ≤ C * (meanu (law d ν) n + Real.log n)

/-- The statement of `Audit/Growth/Challenge.lean`. -/
def growth : Prop :=
  ∀ (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration)
    (hGreenNorms : External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν),
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
      (∀ t : ℕ,
        c * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) ≤ S (law d ν) t ∧
          S (law d ν) t ≤ C * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)))) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * Real.log n) ∧
      (∀ t : ℕ,
        c / ((t : ℝ) + 1) ≤ S (law d ν) t ∧
          S (law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1)))

/-- The statement of `Audit/Trichotomy/Challenge.lean`. -/
def trichotomy : Prop :=
  ∀ (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration)
    (hGreenNorms : External.GreenNorms) (d : ℕ) (hd : 1 ≤ d),
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
        meanu (law d ν) n) atTop atTop)

/-- The statement of `Audit/Nearest/Challenge.lean`. -/
def nearest : Prop :=
  ∀ (hGrowth : External.SandpileGrowth)
    (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration)
    (hGreenNorms : External.GreenNorms)
    (hOdometer : External.SpatialOdometerScaling)
    (hInterior : External.HeatInteriorRegularity)
    (hMinimum : External.HeatStrongMinimum)
    (hCompact : External.HeatCompactness)
    (hLower : External.CriticalScaleLowerTail)
    (hVar : External.VarianceScale)
    (hBerry : External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : CriticalLaw ν),
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal)
      atTop (𝓝 0)

/-- The statement of `Audit/NearestCounterexample/Challenge.lean`. -/
def nearest_counterexample : Prop :=
  ∀ (hBernstein : External.Bernstein) (d : ℕ)
    (hd : 5 ≤ d),
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal) atTop

/-- The statement of `Audit/Near/Challenge.lean`. -/
def near : Prop :=
  ∀ (hGrowth : External.SandpileGrowth)
    (hConcentration : External.UConcentration)
    (hGreen : External.GreenNorms) (hBernstein : External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (ν : ℝ → Measure ℤ)
    (hprob : ∀ δ ∈ Set.Icc 0 δ₀, IsProbabilityMeasure (ν δ))
    (hmean : ∀ δ ∈ Set.Icc 0 δ₀, ∫ k, (k : ℝ) ∂(ν δ) = -δ)
    (hnonconst : ∀ k : ℤ, ν 0 {k} ≠ 1)
    (θ M : ℝ) (hθ : 0 < θ)
    (hexp : ∀ δ ∈ Set.Icc 0 δ₀, Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) ∧
      ∫ k, Real.exp (θ * |(k : ℝ)|) ∂(ν δ) ≤ M)
    (K : ℝ) (hcouple : ∀ δ ∈ Set.Ioc 0 δ₀, ∃ π : Measure (ℤ × ℤ), IsProbabilityMeasure π ∧
      π.map Prod.fst = ν δ ∧ π.map Prod.snd = ν 0 ∧
      ∫ p, |((p.1 : ℝ) - p.2)| ∂π ≤ K * δ),
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Set.Ioc 0 δ₁,
      ENNReal.ofReal (c * nearRate d δ) ≤ meanUlimit (law d (ν δ)) ∧
        meanUlimit (law d (ν δ)) ≤ ENNReal.ofReal (C * nearRate d δ)

/-- The statement of `Audit/OrientedWalk/Challenge.lean`. -/
def oriented_walk : Prop :=
  ∀ (hBern : External.Bernstein)
    (hConc : External.UConcentration)
    (hStability : External.OrientedStoppingStability)
    (hBinomial : External.BinomialLocalCLT)
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν),
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
        meanuOriented (orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => S (orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1))

end ParkingAudit.Statements
