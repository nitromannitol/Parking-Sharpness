import Parking.Frozen.SubcriticalTail
import Parking.Frozen.Master
import Parking.Frozen.Growth
import Parking.Frozen.Trichotomy
import Parking.Frozen.Nearest
import Parking.Frozen.NearestCounterexample
import Parking.Frozen.Near
import Parking.Frozen.OrientedWalk
import Parking.External.Stopping

/-!
# Main results

The main theorems of the formalization of *Sharpness and critical scaling of parking*
(Bou-Rabee and Panagiotis, arXiv:2609.02820), stated here in full: the eight results of the
introduction, Theorems 1.1, 1.2 and 1.4 to 1.8 and Corollary 1.3.

Each theorem below restates its certified counterpart in `Parking/Frozen/` and is proved by
`exact` of it, so the statements displayed in this file are the certified ones.  The one change
is in Theorems 1.4 and 1.7: the certified statements `Parking.Frozen.trichotomy` and
`Parking.Frozen.near` take the optimal stopping representation of the divisible sandpile
odometer (`External.Stopping`, quoted from Bou-Rabee, Peres and Sava-Huss) as a
hypothesis, and here it is discharged by `Parking.External.stopping`, which proves it from the
shared library.  The remaining hypotheses named `External.*` are results the paper cites without
proof; they are assumed, not proved, and are listed with their statements in `ASSUMPTIONS.md`.

* `Parking.subcritical_tail`: below the critical density, `S_t` decays like
  `exp(-t^{d/(d+2)})`, with matching upper and lower bounds.
* `Parking.master`: at the critical density, `E U_n(0) ≍ E u_n(0) + log n` for `n ≥ 2`.
* `Parking.growth`: `E U_n(0) ≍ n^{(4-d)/4}` and `S_t ≍ t^{-d/4}` for `d ≤ 3`, and
  `E U_n(0) ≍ log n` for `d ≥ 4`.
* `Parking.trichotomy`: the quenched comparison of `U_n(0)` and `u_n(0)` in `d ≤ 3`, `d = 4`
  and `d ≥ 5`.
* `Parking.nearest`: for `d ≤ 3` the chance that the origin is closer to an unfilled hole than
  to an active particle after round `t` tends to zero.
* `Parking.nearest_counterexample`: for `d ≥ 5` there is a three-point law for which that chance
  stays bounded below.
* `Parking.near`: `E U_∞(0)` diverges at the rate `nearRate d δ` as the mean `-δ` rises to zero.
* `Parking.oriented_walk`: the growth of `E U_n(0)` for the oriented walk, with the constant
  of the limit in `d = 2`.

All eight reduce to the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see
`Parking/Meta/AxiomsAudit.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- **Theorem 1.1** (`thm:subcritical-tail`).  The certified statement is
`Parking.Frozen.subcritical_tail`. -/
theorem Parking.subcritical_tail
    (hDV : Parking.External.DonskerVaradhanRange)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ Parking.S (Parking.law d ν) t ∧
        Parking.S (Parking.law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) := by
  exact Parking.Frozen.subcritical_tail hDV d hd ν hprob hint hmean hpos θ hθ hexp

/-- **Theorem 1.2** (`thm:master`).  The certified statement is
`Parking.Frozen.master`. -/
theorem Parking.master (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (Parking.meanu (Parking.law d ν) n + Real.log n) ≤ Parking.meanU (Parking.law d ν) n ∧
        Parking.meanU (Parking.law d ν) n ≤
            C * (Parking.meanu (Parking.law d ν) n + Real.log n) := by
  exact Parking.Frozen.master hGrowth hBernstein d hd ν hprob hnonconst
    hmean θ hθ hexp

/-- **Corollary 1.3** (`cor:growth`).  The certified statement is
`Parking.Frozen.growth`. -/
theorem Parking.growth (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
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
          Parking.S (Parking.law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1))) := by
  exact Parking.Frozen.growth hGrowth hBernstein d hd ν hν

/-- **Theorem 1.4** (`thm:trichotomy`).  The certified statement is
`Parking.Frozen.trichotomy`; the stopping representation is discharged. -/
theorem Parking.trichotomy (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
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
        Parking.meanu (Parking.law d ν) n) atTop atTop) := by
  exact Parking.Frozen.trichotomy hGrowth hBernstein
    Parking.External.stopping d hd

/-- **Theorem 1.5** (`thm:nearest`).  The certified statement is
`Parking.Frozen.nearest`. -/
theorem Parking.nearest (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hCompact : Parking.External.HeatCompactness)
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) := by
  exact Parking.Frozen.nearest hGrowth hBernstein hOdometer hInterior
    hCompact hBerry d hd hd3 ν hν

/-- **Theorem 1.6** (`thm:nearest-counterexample`).  The certified statement is
`Parking.Frozen.nearest_counterexample`. -/
theorem Parking.nearest_counterexample (hBernstein : Parking.External.Bernstein) (d : ℕ)
    (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((Parking.law d (Parking.threePointLaw p)) {ω | Parking.HoleCloser ω t}).toReal) atTop := by
  exact Parking.Frozen.nearest_counterexample hBernstein d hd

/-- **Theorem 1.7** (`thm:near`).  The certified statement is
`Parking.Frozen.near`; the stopping representation is discharged. -/
theorem Parking.near (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
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
        Parking.meanUlimit (Parking.law d (ν δ)) ≤ ENNReal.ofReal (C * Parking.nearRate d δ) := by
  exact Parking.Frozen.near hGrowth Parking.External.stopping hBernstein d hd
    δ₀ hδ₀ ν hprob hmean hnonconst θ M hθ hexp K hcouple

/-- **Theorem 1.8** (`thm:oriented-walk`).  The certified statement is
`Parking.Frozen.oriented_walk`. -/
theorem Parking.oriented_walk (hBern : Parking.External.Bernstein)
    (hStability : Parking.External.OrientedStoppingStability)
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
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) := by
  exact Parking.Frozen.oriented_walk hBern hStability d hd ν hν
