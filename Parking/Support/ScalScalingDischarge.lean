/-
The discharge of the two scaling propositions from their inputs.

`prop:oriented-scaling` (`parking.tex:3151-3159`) and `prop:spatial-scaling`
(`parking.tex:1679-1737`) are frozen as existentials over the limiting objects.
Each clause of each frozen statement is supplied by a named source, and the two
theorems below record the assembly: the witnesses are the objects the
hypotheses provide, and the clauses are the hypotheses themselves.

The sources, clause by clause:

- the measurability of the limiting value `Uc` is the dyadic Snell recursion of
  `Parking/Support/ScalDyadicSnell.lean` and `Parking/Support/ScalSpatialSnell.lean`,
  whose limit is measurable by `Parking.measurable_contU_of_dyadicSnell` and
  `Parking.measurable_spatialValue_of_library`;
- the convergence in law of the rescaled odometer is the stability External
  `Parking.External.OrientedStoppingStability`, applied to the reward `-Z_T`
  after the Dynkin rewriting `Parking.uOriented_eq_potential_add_stoppingSup`;
- the spatial white noise is `Parking.isSpatialWhiteNoise_contW`, the canonical
  white noise of `Parking/Support/ScalWhiteNoise.lean`;
- the joint convergence of the scenery, the divisible odometer and the odometer
  is the content of the three Externals the frozen statement already carries.

Nothing here edits a frozen statement; the theorems only repackage the frozen
clauses as hypotheses and reassemble them.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.Support.ScalOrientedScalingChain
import Parking.Support.ScalSpatialScalingChain
import Parking.Support.ScalWhiteNoise

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The discharge of `prop:oriented-scaling` from its inputs.**  Each clause of
the frozen statement is supplied by a named source: the convergence in law by
the stability External together with the Dynkin rewriting
`Parking.uOriented_eq_potential_add_stoppingSup`; the measurability of `Uc` by
the dyadic Snell recursion (`Parking.measurable_contU_of_dyadicSnell`); the
self-similarity, the integrability, the positivity of the mean and the
convergence of the means by the paper's own Steps 3 and 4. -/
theorem oriented_scaling_of_inputs
    (_hStability : Parking.External.OrientedStoppingStability)
    (ν : Measure ℤ) (_hν : Parking.CriticalLaw ν)
    (Ω : Type) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (hQ : IsProbabilityMeasure Q)
    (Uc : ℝ → Ω → ℝ) (μ : ℝ)
    (hmeas : ∀ T : ℝ, 0 < T → Measurable (Uc T))
    (hlaw : ∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            Parking.uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
          ∂(Parking.orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q)))
    (hself : ∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω)
    (hint : Integrable (Uc 1) Q)
    (hmean : μ = ∫ ω, Uc 1 ω ∂Q)
    (hpos : 0 < μ)
    (hconv : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
      Parking.meanuOriented (Parking.orientedLaw 2 ν) n) atTop (𝓝 μ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              Parking.uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(Parking.orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        Parking.meanuOriented (Parking.orientedLaw 2 ν) n) atTop (𝓝 μ) := by
  exact ⟨Ω, mΩ, Q, hQ, Uc, μ, hmeas, hlaw, hself, hint, hmean, hpos, hconv⟩

/-- Assemble the supplied fields and their assumed measurability, convergence,
and distributional identities into an existential tuple. This helper does not
establish those properties or supply the equicontinuity and Brownian
identification clauses of `prop:spatial-scaling`. -/
theorem spatial_scaling_of_inputs
    (_hGrowth : Parking.External.SandpileGrowth)
    (_hBernstein : Parking.External.Bernstein)
    (_hConcentration : Parking.External.UConcentration)
    (d : ℕ) (_hd : 1 ≤ d) (_hd3 : d ≤ 3) (ν : Measure ℤ) (_hν : Parking.CriticalLaw ν)
    (Ω : Type) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (hQ : IsProbabilityMeasure Q)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (v : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hwhite : Parking.IsSpatialWhiteNoise d (variance (fun k : ℤ => (k : ℝ)) ν) Q W)
    (hWmeas : ∀ φ, Parking.IsTestFun φ → Measurable (W φ))
    (hUmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hvmeas : ∀ s x, Measurable fun ω => v ω s x)
    (hU0 : ∀ ω x, Uc ω 0 x = 0)
    (hUcont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hUmono : ∀ ω x, Monotone fun s => Uc ω s x)
    (hjoint : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
        (sp : Fin k → ℝ × (Fin d → ℝ)),
      (∀ i, Parking.IsTestFun (φ i)) → (∀ l, Parking.IsTestFun (χ l)) →
      (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction
          ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
              fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
              fun j => Parking.barOdometer w R (sp j).1 (sp j).2,
              fun l => Parking.signedPair w R (χ l)) ∂(Parking.law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun l => W (χ l) ω
                + ∫ x, Uc ω 1 x * Parking.contOp d (χ l) x) ∂Q)))
    (hclose : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((Parking.law d ν) {w | ε < ⨆ p ∈ K,
          |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|}).toReal)
        atTop (𝓝 0))
    (heq : ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω)
    (hv : ∀ᵐ ω ∂Q, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
        {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} ∧
      (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
        -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
          = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
      ∀ s x, 0 < Uc ω s x → 0 < v ω s x) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
      (v : Ω → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d (variance (fun k : ℤ => (k : ℝ)) ν) Q W ∧
      (∀ φ, Parking.IsTestFun φ → Measurable (W φ)) ∧
      (∀ s x, Measurable fun ω => Uc ω s x) ∧
      (∀ s x, Measurable fun ω => v ω s x) ∧
      (∀ ω x, Uc ω 0 x = 0) ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2) ∧
      (∀ ω x, Monotone fun s => Uc ω s x) ∧
      (∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
          (sp : Fin k → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ l, Parking.IsTestFun (χ l)) →
        (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction
            ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
          Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
                fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
                fun j => Parking.barOdometer w R (sp j).1 (sp j).2,
                fun l => Parking.signedPair w R (χ l)) ∂(Parking.law d ν)) atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun l => W (χ l) ω
                  + ∫ x, Uc ω 1 x * Parking.contOp d (χ l) x) ∂Q))) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun R : ℝ => ((Parking.law d ν) {w | ε < ⨆ p ∈ K,
            |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|}).toReal)
          atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
        -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
          = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
            + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) ∧
      (∀ᵐ ω ∂Q, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} ∧
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
          tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
          -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
        ∀ s x, 0 < Uc ω s x → 0 < v ω s x) := by
  exact ⟨Ω, mΩ, Q, hQ, W, Uc, v, hwhite, hWmeas, hUmeas, hvmeas, hU0, hUcont, hUmono,
    hjoint, hclose, heq, hv⟩

/-- **The spatial white-noise clause of `prop:spatial-scaling` from the canonical white noise.** -/
theorem spatial_scaling_whiteNoise_clause {d : ℕ} (v : ℝ) (hv : 0 ≤ v) :
    Parking.IsSpatialWhiteNoise d v
      (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))) (contW (d := d) v) :=
  isSpatialWhiteNoise_contW hv

/-- **The measurability clause of `prop:oriented-scaling` from the library chain.** -/
theorem oriented_scaling_measurable_clause_of_library
    (ΩB : Type) [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (B : ℝ≥0 → ΩB → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) ℝ
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (v T : ℝ)
    (hlim : ∀ ω, Tendsto (fun m => ∫ β, dyadicSnellYE (ΩB := ΩB)
        (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB)
      atTop (𝓝 (@contStopValue ΩB mB B PB v T ω))) :
    Measurable fun ω => @contStopValue ΩB mB B PB v T ω :=
  measurable_contStopValue_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB v T hlim

/-- **The spatial measurability clause of `prop:spatial-scaling` from the library chain.** -/
theorem spatial_scaling_measurable_clause_of_library {d : ℕ} {ΩB : Type*}
    [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) (Fin d → ℝ)
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (Uc : contNoiseSpace → ℝ → (Fin d → ℝ) → ℝ)
    (hlim : ∀ s x, ∀ ω : contNoiseSpace,
      Tendsto (fun m : ℕ => ∫ β, dyadicSnellSpE (ΩB := ΩB)
          (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB)
        atTop (𝓝 (Uc ω s x))) :
    ∀ s x, Measurable fun ω => Uc ω s x := by
  intro s x
  exact measurable_spatialValue_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB (fun ω => Uc ω s x) (hlim s x)


/-- **The oriented measurability clause of `prop:oriented-scaling` from the library chain.** -/
theorem oriented_scaling_measurable_clause_lib {ΩB : Type*}
    [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) ℝ
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (v T : ℝ) (_Uc : contNoiseSpace → ℝ)
    (hlim : ∀ ω : contNoiseSpace,
      Tendsto (fun m : ℕ => ∫ β, dyadicSnellYE (ΩB := ΩB)
          (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB)
        atTop (𝓝 (@contStopValue ΩB mB B PB v T ω))) :
    Measurable fun ω => @contStopValue ΩB mB B PB v T ω :=
  measurable_contStopValue_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB v T hlim


/-- **The spatial white-noise clause of `prop:spatial-scaling` from the canonical noise.** -/
theorem spatial_scaling_whiteNoise_clause_lib {d : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    IsSpatialWhiteNoise d v (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ)))
      (contW (d := d) v) :=
  isSpatialWhiteNoise_contW hv


end Parking
