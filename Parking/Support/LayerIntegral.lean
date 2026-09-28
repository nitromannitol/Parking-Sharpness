import Parking.Support.LayerReward

/-!
# Resampling one independent layer

A bounded expectation over the product of countably many independent layers can be rewritten
as the average, over the other layers, of the integral over one resampled layer. This is the
single-layer case of the fresh-layer machinery used throughout `Parking.Support`, proved by
transporting through the measure-preserving map that replaces layer `n`.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- Resampling one independent layer expresses a bounded expectation as the average of its
sections. -/
theorem integral_layer_sections {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : (ℕ → α) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ ω, ‖f ω‖ ≤ B) (n : ℕ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ)) =
      ∫ ω, ∫ v, f (Function.update ω n v) ∂μ ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  let P := Measure.infinitePi fun _ : ℕ => μ
  let T : (ℕ → α) × α → ℕ → α := fun q => Function.update q.1 n q.2
  have hT : MeasurePreserving T (P.prod μ) P :=
    measurePreserving_update_infinitePi (fun _ : ℕ => μ) n
  have hi : Integrable (fun q => f (T q)) (P.prod μ) :=
    Integrable.of_bound (hf.comp hT.measurable).aestronglyMeasurable B
      (ae_of_all _ fun q => hB (T q))
  have he := integral_map (μ := P.prod μ) (φ := T) (f := f) hT.measurable.aemeasurable
    (by rw [hT.map_eq]; exact hf.aestronglyMeasurable)
  rw [hT.map_eq] at he
  exact he.trans (integral_prod _ hi)
end Parking
