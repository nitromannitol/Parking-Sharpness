/-
The measurability of the limit object of `prop:spatial-scaling`
(`parking.tex:1679-1737`).

The proposition asserts the joint convergence of the rescaled scenery, the
rescaled divisible odometer and the rescaled odometer to the spatial white
noise and the continuum Brownian optimal-stopping value, together with the
distributional equation on the positivity set.  The chain assembled here is the
measurability half of the limit object, exactly as for
`prop:oriented-scaling`:

1. a jointly continuous modification `Y` of the spatial white noise, from the
   multi-parameter Kolmogorov-Chentsov theorem;
2. the measurability of the spatial dyadic Snell recursion of the value, from
   the joint measurability of the conditional expectation in the noise
   parameter (`LatticeProb.exists_measurable_condExp_param`, carried as an
   explicit hypothesis) and the joint measurability of the modification
   (`Parking.measurable_dyadicSnellSp`);
3. the measurability of the continuum value as the limit of the recursion.

The convergence in law itself is the content of the frozen statement and rests
on the cited inputs `Parking.External.SandpileGrowth`,
`Parking.External.Bernstein` and `Parking.External.UConcentration`, which the
frozen statement already carries as hypotheses.
-/
import Parking.Support.ScalSpatialSnell
import LatticeProb.Prob.CondExpParam
import Parking.Support.Continuum

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The spatial continuum value is measurable once it is the limit of the
spatial dyadic Snell recursion.** -/
theorem measurable_spatialValue_of_tendsto_dyadicSnell {d : ℕ} {ΩB : Type*}
    [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (V : contNoiseSpace → ℝ)
    (hmeas : ∀ m, Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB)
    (hlim : ∀ ω : contNoiseSpace,
      Tendsto (fun m : ℕ => ∫ β, dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB)
        atTop (𝓝 (V ω))) :
    Measurable V :=
  measurable_of_tendsto_metrizable (fun m => hmeas m) (tendsto_pi_nhds.mpr hlim)

/-- **The spatial continuum value is measurable once it is the limit of the
spatial dyadic Snell recursion, with the conditional expectation replaced by the
library's jointly measurable representative.** -/
theorem measurable_spatialValue_of_library {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) (Fin d → ℝ)
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (V : contNoiseSpace → ℝ)
    (hlim : ∀ ω : contNoiseSpace,
      Tendsto (fun m : ℕ => ∫ β, dyadicSnellSpE (ΩB := ΩB)
          (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB)
        atTop (𝓝 (V ω))) :
    Measurable V :=
  measurable_of_tendsto_metrizable
    (fun m => measurable_integral_dyadicSnellSpE_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB m)
    (tendsto_pi_nhds.mpr hlim)

/-- **The measurability clause of `prop:spatial-scaling` from the library
chain.**  The continuum value `Uc` is read at the noise `ω` and the space-time
point `(s,x)`; its measurability in `ω` is the limit of the spatial dyadic Snell
recursion. -/
theorem spatial_scaling_measurable_clause {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    [StandardBorelSpace ΩB]
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
  exact measurable_spatialValue_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB
    (fun ω => Uc ω s x) (fun ω => hlim s x ω)

end Parking
