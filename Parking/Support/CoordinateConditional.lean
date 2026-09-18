/- Conditional averaging of a fresh coordinate in the presence of independent background data. -/
import Parking.Support.CoordinateProductFactor
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical

theorem condExp_mul_fresh_coordinate {Ω ι : Type*} {X : ι → Type*}
    [MeasurableSpace Ω] [DecidableEq ι] [∀ i, MeasurableSpace (X i)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (P i)] (q : ι) (b : X q)
    (m : MeasurableSpace (Ω × (Π i, X i)))
    (hm : m ≤ Prod.instMeasurableSpace)
    (hinv : ∀ S : Set (Ω × (Π i, X i)), MeasurableSet[m] S → ∀ η σ,
      (η, Function.update σ q b) ∈ S ↔ (η, σ) ∈ S)
    (H : Ω × (Π i, X i) → ℝ) (hH : Measurable[m] H)
    (hiH : Integrable H (μ.prod (Measure.infinitePi P)))
    (g : X q → ℝ) (hg : Measurable g)
    (hiHG : Integrable (fun z => H z * g (z.2 q)) (μ.prod (Measure.infinitePi P))) :
    (μ.prod (Measure.infinitePi P))[fun z => H z * g (z.2 q) | m] =ᵐ[μ.prod (Measure.infinitePi P)]
      fun z => H z * ∫ a, g a ∂(P q) := by
  letI : MeasurableSpace (Ω × (Π i, X i)) := Prod.instMeasurableSpace
  have hHa : Measurable H := hH.mono hm le_rfl
  have hHin (η : Ω) (σ : Π i, X i) : H (η, Function.update σ q b) = H (η, σ) := by
    have hs := hH (measurableSet_singleton (H (η, σ)))
    exact (hinv _ hs η σ).mpr rfl
  have hci : Integrable (fun z => H z * ∫ a, g a ∂(P q)) (μ.prod (Measure.infinitePi P)) :=
    hiH.mul_const _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ.prod (Measure.infinitePi P))
    (g := fun z => H z * ∫ a, g a ∂(P q)) hm hiHG (fun _ _ _ => hci.integrableOn)
    (fun S hS _ => ?_) (hH.mul_const _).stronglyMeasurable.aestronglyMeasurable).symm
  have hSa : MeasurableSet S := hm S hS
  let F : Ω × (Π i, X i) → ℝ := Set.indicator S H
  have hF : Measurable F := hHa.indicator hSa
  have hiF : Integrable F (μ.prod (Measure.infinitePi P)) := hiH.indicator hSa
  have he : (fun z => F z * g (z.2 q)) = Set.indicator S (fun z => H z * g (z.2 q)) := by
    funext z
    by_cases hz : z ∈ S <;> simp [F, hz]
  have hiFG : Integrable (fun z => F z * g (z.2 q)) (μ.prod (Measure.infinitePi P)) := by
    rw [he]
    exact hiHG.indicator hSa
  have hFi (η : Ω) (σ : Π i, X i) : F (η, Function.update σ q b) = F (η, σ) := by
    by_cases hz : (η, σ) ∈ S
    · have hzu := (hinv S hS η σ).mpr hz
      simp only [F, Set.indicator_of_mem hz, Set.indicator_of_mem hzu, hHin]
    · have hzu : (η, Function.update σ q b) ∉ S := fun h => hz ((hinv S hS η σ).mp h)
      simp only [F, Set.indicator_of_notMem hz, Set.indicator_of_notMem hzu]
  have hfactor := integral_mul_coordinate_prod_of_update_invariant μ P q b F hF hiF hFi g hg hiFG
  rw [he, integral_indicator hSa] at hfactor
  have hFH : (∫ z, F z ∂(μ.prod (Measure.infinitePi P))) = ∫ z in S, H z ∂(μ.prod (Measure.infinitePi P)) :=
    integral_indicator hSa
  rw [hFH] at hfactor
  rw [integral_mul_const]
  exact hfactor.symm

end Parking
