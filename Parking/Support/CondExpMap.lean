/-
Conditioning on the σ-algebra a measurable map pulls back.

A variable that is a function of an exploration is a function of the sequence
the exploration reveals, and its conditional expectation given the first few
revealed values is computed downstream, in the product space that sequence
lives in.  What carries the answer back is that conditioning on
`MeasurableSpace.comap Φ G` is conditioning on `G` after the pushforward and
reading the result through `Φ`.
-/
import Parking.Support.Error

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Parking

/-- **A conditional expectation transported along a measurable map.**
Conditioning on the σ-algebra a map pulls back is conditioning downstream and
reading the answer back through the map.  This is what lets a variable defined
from an exploration be computed in the product space the exploration lands
in. -/
theorem condExp_comap_map {Ω Ω' : Type*} [MeasurableSpace Ω] {G : MeasurableSpace Ω'}
    [m0 : MeasurableSpace Ω'] (hG : G ≤ m0)
    (P : Measure Ω) [IsFiniteMeasure P] (Φ : Ω → Ω') (hΦ : Measurable Φ)
    (f : Ω' → ℝ) (hf : Integrable f (P.map Φ)) :
    P[fun ω => f (Φ ω) | MeasurableSpace.comap Φ G]
      =ᵐ[P] fun ω => ((P.map Φ)[f | G]) (Φ ω) := by
  classical
  have hcomap : MeasurableSpace.comap Φ G ≤ (inferInstanceAs (MeasurableSpace Ω)) := by
    rintro A ⟨B, hB, rfl⟩
    exact hΦ (hG B hB)
  have hfΦ : Integrable (fun ω => f (Φ ω)) P :=
    (integrable_map_measure hf.aestronglyMeasurable hΦ.aemeasurable).mp hf
  have hcond : Integrable ((P.map Φ)[f | G]) (P.map Φ) := integrable_condExp
  have hcondΦ : Integrable (fun ω => ((P.map Φ)[f | G]) (Φ ω)) P :=
    (integrable_map_measure hcond.aestronglyMeasurable hΦ.aemeasurable).mp hcond
  have hΦmeas : Measurable[MeasurableSpace.comap Φ G, G] Φ :=
    measurable_iff_comap_le.mpr le_rfl
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hcomap hfΦ
    (fun A _ _ => hcondΦ.integrableOn) ?_ ?_).symm
  · rintro A ⟨B, hB, rfl⟩ -
    have h1 : ∫ ω in Φ ⁻¹' B, f (Φ ω) ∂P = ∫ y in B, f y ∂(P.map Φ) :=
      (setIntegral_map (hG B hB) hf.aestronglyMeasurable hΦ.aemeasurable).symm
    have h2 : ∫ y in B, f y ∂(P.map Φ) = ∫ y in B, ((P.map Φ)[f | G]) y ∂(P.map Φ) :=
      (setIntegral_condExp hG hf hB).symm
    have h3 : ∫ y in B, ((P.map Φ)[f | G]) y ∂(P.map Φ)
        = ∫ ω in Φ ⁻¹' B, ((P.map Φ)[f | G]) (Φ ω) ∂P :=
      setIntegral_map (hG B hB) hcond.aestronglyMeasurable hΦ.aemeasurable
    rw [← h3, ← h2, ← h1]
  · exact (stronglyMeasurable_condExp.comp_measurable hΦmeas).aestronglyMeasurable

end Parking

end
