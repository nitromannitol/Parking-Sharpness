import Parking.MainTheorems
import Parking.External.BernsteinProved

/-!
# Main results with the Bernstein estimate

The martingale Bernstein estimate is supplied in each result.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.growth_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
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
          Parking.S (Parking.law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1))) :=
  Parking.growth hGrowth Parking.External.bernstein d hd ν hν

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.trichotomy_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
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
        Parking.meanu (Parking.law d ν) n) atTop atTop) :=
  Parking.trichotomy hGrowth Parking.External.bernstein d hd

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.nearest_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hCompact : Parking.External.HeatCompactness)
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) :=
  Parking.nearest hGrowth Parking.External.bernstein hOdometer hInterior hCompact hBerry
    d hd hd3 ν hν

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.nearest_heat_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) :=
  Parking.nearest' hGrowth Parking.External.bernstein hOdometer hBerry d hd hd3 ν hν

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.nearest_stability_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) :=
  Parking.nearest'' hGrowth Parking.External.bernstein hStab hBerry d hd hd3 ν hν

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.nearest_lower_bound_of_bernstein (d : ℕ)
    (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((Parking.law d (Parking.threePointLaw p)) {ω | Parking.HoleCloser ω t}).toReal) atTop :=
  by
    have h : Parking.External.Bernstein := Parking.External.bernstein
    exact?

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.near_of_bernstein (hGrowth : Parking.External.SandpileGrowth)
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
        Parking.meanUlimit (Parking.law d (ν δ)) ≤ ENNReal.ofReal (C * Parking.nearRate d δ) :=
  Parking.near hGrowth Parking.External.bernstein d hd δ₀ hδ₀ ν hprob hmean hnonconst
    θ M hθ hexp K hcouple

/-- The result with the Bernstein estimate supplied. -/
theorem Parking.oriented_walk_of_bernstein (hStability : Parking.External.OrientedStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
        Parking.meanuOriented (Parking.orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => Parking.S (Parking.orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) :=
  Parking.oriented_walk Parking.External.bernstein hStability d hd ν hν
