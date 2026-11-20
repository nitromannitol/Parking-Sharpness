import Parking.Frozen.OrientedScaling
import Parking.External.OrientedStoppingStabilityUnconditional

/-!
# The oriented scaling limit without hypotheses

The oriented scaling limit (`prop:oriented-scaling`) holds with no cited hypothesis: the
oriented stopping stability is `Parking.External.orientedStoppingStability_holds`.
-/

open MeasureTheory Filter Topology

/-- The oriented scaling limit (`prop:oriented-scaling`) with no cited hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.oriented_scaling_proved
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
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
        Parking.meanuOriented (Parking.orientedLaw 2 ν) n) atTop (𝓝 μ)
-- FROZEN-STATEMENT-END
:=
  Parking.Frozen.oriented_scaling Parking.External.orientedStoppingStability_holds ν hν
