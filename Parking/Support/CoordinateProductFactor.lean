/- A fresh product coordinate factors from an independent background and unrevealed observations. -/
import Parking.Support.CoordinateFactor

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

theorem integral_mul_coordinate_prod_of_update_invariant {Ω ι : Type*} {X : ι → Type*}
    [MeasurableSpace Ω] [DecidableEq ι] [∀ i, MeasurableSpace (X i)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (P i)] (q : ι) (b : X q)
    (F : Ω × (Π i, X i) → ℝ) (hF : Measurable F)
    (hiF : Integrable F (μ.prod (Measure.infinitePi P)))
    (hinv : ∀ η σ, F (η, Function.update σ q b) = F (η, σ))
    (g : X q → ℝ) (hg : Measurable g)
    (hiFG : Integrable (fun z => F z * g (z.2 q)) (μ.prod (Measure.infinitePi P))) :
    (∫ z, F z * g (z.2 q) ∂(μ.prod (Measure.infinitePi P))) =
      (∫ z, F z ∂(μ.prod (Measure.infinitePi P))) * ∫ a, g a ∂(P q) := by
  rw [integral_prod _ hiFG, integral_prod _ hiF, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun η =>
    integral_mul_coordinate_of_update_invariant P q b (fun σ => F (η, σ))
      (hF.comp (measurable_const.prodMk measurable_id)) (hinv η) g hg

end Parking
