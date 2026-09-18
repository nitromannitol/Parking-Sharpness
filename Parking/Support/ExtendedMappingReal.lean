/-
**The extended continuous mapping theorem, real parameter.**

`Parking.Support.ExtendedMapping.extended_continuous_mapping` and
`tendsto_integral_comp_of_locally_uniform` are stated for a SEQUENCE of laws and maps,
indexed by `ℕ`.  Every convergence clause of `prop:spatial-scaling`
(`Parking/Frozen/SpatialScaling.lean`) is stated for the REAL parameter `R → ∞`
(`Filter.atTop` on `ℝ`), matching `parking.tex`'s own "as `R → ∞`".  This file supplies the
bridge: `(atTop : Filter ℝ)` is countably generated (`ℝ` is an Archimedean ordered field,
`Filter.atTop_isCountablyGenerated_of_archimedean`), so a real-parameter limit is equivalent
to the same limit along every sequence tending to `atTop`
(`Filter.tendsto_iff_seq_tendsto`), which reduces the real-parameter statement to one
application of the `ℕ`-indexed theorem per sequence.

The Lipschitz form (`locallyUniform_of_lipschitz`) is what every application in this
repository needs (optimal-stopping values are `1`-Lipschitz in the reward,
`Parking.abs_stoppingSup_sub_le`/`Parking.Support.ExtendedMapping.locallyUniform_of_lipschitz`
already recorded this design), so it is the form proved here; the general local-uniform
form transfers by the identical argument if a future application needs it.
-/
import Parking.Support.ExtendedMapping

open MeasureTheory Filter Topology

noncomputable section

namespace Parking

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **The extended continuous mapping theorem, real parameter, Lipschitz form.**  If the
laws `νR R` converge weakly to `ν` as `R → ∞` (real parameter) and the Borel functions
`fR R` are uniformly (in `R`) `1`-Lipschitz and converge pointwise to `f` as `R → ∞`, then
the image laws converge weakly on the line, as `R → ∞`. -/
theorem tendsto_integral_comp_real_of_lipschitz
    (ν : Measure E) [IsProbabilityMeasure ν] (νR : ℝ → Measure E)
    [∀ R, IsProbabilityMeasure (νR R)]
    (hlim : ∀ G : BoundedContinuousFunction E ℝ,
      Tendsto (fun R : ℝ => ∫ x, G x ∂(νR R)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → ℝ) (fR : ℝ → E → ℝ)
    (hfR : ∀ R, Measurable (fR R)) (hf : Measurable f)
    (hLip : ∀ (R : ℝ) (y x : E), |fR R y - fR R x| ≤ dist y x)
    (hpt : ∀ x : E, Tendsto (fun R => fR R x) atTop (𝓝 (f x)))
    (G : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun R : ℝ => ∫ x, G (fR R x) ∂(νR R)) atTop (𝓝 (∫ x, G (f x) ∂ν)) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro r hr
  have hlim' : ∀ G' : BoundedContinuousFunction E ℝ,
      Tendsto (fun n : ℕ => ∫ x, G' x ∂(νR (r n))) atTop (𝓝 (∫ x, G' x ∂ν)) := fun G' =>
    (hlim G').comp hr
  have hLip' : ∀ (n : ℕ) (y x : E), |fR (r n) y - fR (r n) x| ≤ dist y x :=
    fun n => hLip (r n)
  have hpt' : ∀ x : E, Tendsto (fun n => fR (r n) x) atTop (𝓝 (f x)) :=
    fun x => (hpt x).comp hr
  haveI : ∀ n : ℕ, IsProbabilityMeasure (νR (r n)) := fun n => inferInstance
  exact tendsto_integral_comp_of_locally_uniform ν (fun n => νR (r n)) hlim' f
    (fun n => fR (r n)) (fun n => hfR (r n)) hf
    (fun x _ hε => locallyUniform_of_lipschitz (fun n => fR (r n)) f hLip' hpt' x hε) G

end Parking

end
