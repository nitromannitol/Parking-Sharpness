/-
The chain of `prop:oriented-scaling` (`parking.tex:3151-3222`), assembled from
the inputs the repository has and the inputs it is still owed.

The paper's proof builds the limit random variable
`U(T) = Z_T(0,0) + sup_{τ≤T} E_0[-Z_T(τ,B_τ)]` and then needs three things
beyond the field itself:

1. a jointly continuous version of the noise field `Z_T` (so that the
   integrand of a stopping time is measurable and the payoffs are genuine);
2. a canonical Brownian space with its dyadic filtrations, and the joint
   measurability in a parameter of a conditional expectation, so that the
   dyadic Snell recursion of the value exists;
3. the stability of optimal-stopping values under uniform convergence of
   uniformly bounded rewards, which is the cited input
   `Parking.External.OrientedStoppingStability`.

Item 1 is discharged in `Parking/Support/ScalNoiseModification.lean` from the
multi-parameter Kolmogorov-Chentsov theorem of the library.  Items 2 and 3 are
carried here as explicit hypotheses, in the shape the frozen statement needs,
until the canonical Wiener space and the joint-measurability lemma land.
-/
import Parking.Support.ScalNoiseModification
import Parking.Support.ContStopGeneral
import Parking.External.OrientedStoppingStability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The limit random variable is measurable once its stopping part is.**
`U(T) = Z_T(0,0) + sup_{τ≤T} E_0[-Z_T(τ,B_τ)]` is the sum of the field at the
origin, which is measurable, and the value, which is the hypothesis. -/
theorem measurable_contU_of_measurable_contStopValue {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) (v T : ℝ)
    (h : Measurable fun ω => contStopValue B PB v T ω) :
    Measurable fun ω => contU B PB v T ω := by
  unfold contU
  exact (measurable_contZ v T 0 0).add h

/-- **The Brownian value is bounded by the uniform bound on the reward.** -/
theorem contValue_le_of_abs_le {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {G : ℝ → ℝ → ℝ} {T M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s y : ℝ, |G s y| ≤ M) :
    contValue B PB G T ≤ M :=
  contValue_le B PB G T hM (fun s y => (abs_le.mp (hbound s y)).2)

end Parking
