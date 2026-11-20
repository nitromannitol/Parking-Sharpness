import Parking.Support.ContStopGeneral
import Sandpile.Continuum.Stopping

/-!
# One-dimensional Brownian motion for the oriented walk

The oriented scaling limit has one quarter of the variance of a standard
Brownian motion. The coordinate map `x - 2B` gives the standard normalization
at every starting point and recovers `B` by the inverse map at the origin.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- A one-dimensional Brownian family obtained from a quarter Brownian motion. -/
def orientedBrownianFamily {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (x : Sandpile.Continuum.Space 1) (t : ℝ≥0) (ω : Ω) : Sandpile.Continuum.Space 1 :=
  WithLp.toLp 2 (fun i : Fin 1 => x i - 2 * B t ω)

/-- The inverse coordinate map recovers the original motion at zero. -/
theorem orientedBrownianFamily_zero_coord {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    -(orientedBrownianFamily B 0 t ω 0) / 2 = B t ω := by
  simp [orientedBrownianFamily]

/-- The family has the standard one-dimensional Brownian normalization. -/
theorem isBrownian_orientedBrownianFamily {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsQuarterBrownian B P) (x : Sandpile.Continuum.Space 1) :
    Sandpile.Continuum.IsBrownian 1 x (orientedBrownianFamily B x) P where
  start := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h
    ext i
    simp only [orientedBrownianFamily, WithLp.ofLp_toLp, Pi.sub_apply]
    linarith
  coord := fun i => by
    have heq : (fun t ω => Real.sqrt ((1 : ℕ) : ℝ) *
        (orientedBrownianFamily B x t ω i - x i)) = -(fun t ω => 2 * B t ω) := by
      funext t ω
      simp [orientedBrownianFamily]
    rw [heq]
    exact hB.neg
  indep := iIndepFun.of_subsingleton

/-- The family and the original real process generate the same information at
    each time. -/
theorem brownianFiltration_orientedBrownianFamily_eq {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (x : Sandpile.Continuum.Space 1) (t : ℝ≥0) :
    Sandpile.Continuum.brownianFiltration (orientedBrownianFamily B x) t = pathSigma B t := by
  have hcomap : ∀ s, MeasurableSpace.comap (orientedBrownianFamily B x s)
      (inferInstance : MeasurableSpace (Sandpile.Continuum.Space 1)) =
      MeasurableSpace.comap (B s) inferInstance := by
    intro s
    apply le_antisymm
    · apply Measurable.comap_le
      have hm : @Measurable Ω ℝ (MeasurableSpace.comap (B s) inferInstance) _ (B s) :=
        measurable_iff_comap_le.mpr le_rfl
      have hf : Measurable (fun r : ℝ =>
          (WithLp.toLp 2 (fun i : Fin 1 => x i - 2 * r) : Sandpile.Continuum.Space 1)) := by
        fun_prop
      exact hf.comp hm
    · apply Measurable.comap_le
      have hm : @Measurable Ω (Sandpile.Continuum.Space 1)
          (MeasurableSpace.comap (orientedBrownianFamily B x s) inferInstance) _
          (orientedBrownianFamily B x s) := measurable_iff_comap_le.mpr le_rfl
      have hcoord : Measurable (fun y : Sandpile.Continuum.Space 1 => (x 0 - y 0) / 2) := by
        fun_prop
      have heq : (fun ω => (x 0 - orientedBrownianFamily B x s ω 0) / 2) = B s := by
        funext ω
        simp [orientedBrownianFamily]
      rw [← heq]
      exact hcoord.comp hm
  show (⨆ s ≤ t, MeasurableSpace.comap (orientedBrownianFamily B x s) _) =
    ⨆ s ≤ t, MeasurableSpace.comap (B s) _
  simp only [hcomap]

/-- The stopping classes agree under the invertible coordinate transformation. -/
theorem isBrownianStopping_orientedBrownianFamily_iff {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (x : Sandpile.Continuum.Space 1) (τ : Ω → ℝ≥0) :
    Sandpile.Continuum.IsBrownianStopping (orientedBrownianFamily B x) τ ↔
      IsNaturalStopping B τ := by
  unfold Sandpile.Continuum.IsBrownianStopping IsStoppingTime IsNaturalStopping
  refine forall_congr' fun t => ?_
  rw [brownianFiltration_orientedBrownianFamily_eq]
  have hset : {ω | ((τ ω : ℝ≥0∞) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {ω | τ ω ≤ t} := Set.ext fun ω => WithTop.coe_le_coe
  change MeasurableSet[pathSigma B t]
    {ω | ((τ ω : ℝ≥0∞) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} ↔ _
  rw [hset]

end Parking
