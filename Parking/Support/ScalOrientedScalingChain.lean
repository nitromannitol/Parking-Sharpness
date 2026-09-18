/-
The discharge of `prop:oriented-scaling` (`parking.tex:3151-3222`) from library
inputs and the two further inputs named at the end of this comment.

The paper's Step 1 builds the limit random variable
`U(T) = Z_T(0,0) + sup_{τ≤T} E_0[-Z_T(τ,B_τ)]` and Step 2 makes it measurable
and identifies its law.  The chain assembled here is:

1. a jointly continuous modification `Y` of the noise field, from the
   multi-parameter Kolmogorov-Chentsov theorem
   (`Parking.exists_continuous_modification_contZ`);
2. the measurability of the dyadic Snell recursion of the value, from the
   joint measurability of the conditional expectation in the noise parameter
   (a result of the shared library, carried as an explicit hypothesis) and
   the joint measurability of the modification (`Parking.measurable_dyadicSnellY`);
3. the measurability of the continuum value as the limit of the recursion
   (`Parking.measurable_contStopValue_of_tendsto_dyadicSnell`), and hence of
   `U(T)` (`Parking.measurable_contU_of_measurable_contStopValue`);
4. the uniform bound on the recursion that the stability estimate needs
   (`Parking.abs_integral_dyadicSnellY_le`).

The stability External `Parking.External.OrientedStoppingStability` and the
Dynkin rewriting `Parking.uOriented_eq_potential_add_stoppingSup` are the two
further inputs of the frozen statement; combining them with the chain above
discharges the frozen proposition (`Parking/Support/ScalScalingDischarge.lean`).
-/
import Parking.Support.ScalDyadicSnell
import Parking.Support.ScalOrientedChain
import Parking.Support.ContOrientedLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The continuum stopping value is measurable once it is the limit of the
dyadic Snell recursion.**  The paper's Step 2 identifies the value with the
limit of the dyadic recursion as the mesh refines; a pointwise limit of
measurable functions is measurable. -/
theorem measurable_contStopValue_of_tendsto_dyadicSnell {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) (v T : ℝ)
    (𝒢 : ℕ → MeasurableSpace ΩB) (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hmeas : ∀ m, Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB)
    (hlim : ∀ ω : contNoiseSpace,
      Tendsto (fun m : ℕ => ∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB)
        atTop (𝓝 (contStopValue B PB v T ω))) :
    Measurable fun ω => contStopValue B PB v T ω :=
  measurable_of_tendsto_metrizable (fun m => hmeas m) (tendsto_pi_nhds.mpr hlim)

/-- **The continuum value `U(T)` is measurable** from the measurability of its
stopping part and the measurability of the field at the origin. -/
theorem measurable_contU_of_dyadicSnell {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) (v T : ℝ)
    (𝒢 : ℕ → MeasurableSpace ΩB) (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hmeas : ∀ m, Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB)
    (hlim : ∀ ω : contNoiseSpace,
      Tendsto (fun m : ℕ => ∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB)
        atTop (𝓝 (contStopValue B PB v T ω))) :
    Measurable fun ω => contU B PB v T ω :=
  measurable_contU_of_measurable_contStopValue B PB v T
    (measurable_contStopValue_of_tendsto_dyadicSnell B PB v T 𝒢 Y hmeas hlim)

/-- **The measurability clause of `prop:oriented-scaling` from the library chain.** -/
theorem oriented_scaling_measurable_clause
    (ν : Measure ℤ) (_hν : Parking.CriticalLaw ν)
    (ΩB : Type) [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (B : ℝ≥0 → ΩB → ℝ) (hB : @Measurable (ℝ≥0 × ΩB) ℝ (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (v T : ℝ) (_hT : 0 < T)
    (hlim : ∀ ω, Tendsto (fun m => ∫ β, dyadicSnellYE (ΩB := ΩB)
        (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB)
      atTop (𝓝 (@contStopValue ΩB mB B PB v T ω))) :
    Measurable fun ω => @contU ΩB mB B PB v T ω :=
  (measurable_contZ v T 0 0).add
    (measurable_contStopValue_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB v T hlim)


end Parking
