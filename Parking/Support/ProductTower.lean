import Parking.Support.ProductSection

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- For bounded functionals the tower identity holds at every retained configuration. -/
theorem partialInt_tower (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (hST : S ⊆ T)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F) (B : ℝ) (hB : ∀ ω, |F ω| ≤ B)
    (ω : Π i, X i) : partialInt μ S (partialInt μ T F) ω = partialInt μ S F ω := by
  let P := Measure.infinitePi μ
  let f : (Π i, X i) → ℝ := fun η => F (comb S ω η)
  have hfm : Measurable f := hFm.comp ((measurable_comb S).comp (measurable_const.prodMk measurable_id))
  have hi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable B (ae_of_all _ fun η => hB _)
  have he (η ζ : Π i, X i) : comb T (comb S ω η) ζ = comb S ω (comb T η ζ) := by
    funext i
    by_cases hi : i ∈ S
    · simp [comb, hi, hST hi]
    · simp [comb, hi]
  change (∫ η, ∫ ζ, F (comb T (comb S ω η) ζ) ∂P ∂P) = ∫ η, f η ∂P
  simp_rw [he]
  rw [← integral_prod _ (integrable_comp_comb μ T hi)]
  have hp := measurePreserving_comb μ T
  rw [← integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable, hp.map_eq]

/-- Adding a single retained coordinate identifies the preceding mean with its one-coordinate average. -/
theorem partialInt_insert_coordinate [DecidableEq ι]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] (j : ι) (hj : j ∉ S)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F) (B : ℝ) (hB : ∀ ω, |F ω| ≤ B)
    (ω : Π i, X i) :
    partialInt μ S F ω = ∫ a, partialInt μ (insert j S) F (Function.update ω j a) ∂(μ j) := by
  rw [← partialInt_tower μ S (insert j S) (Set.subset_insert j S) F hFm B hB ω]
  apply partialInt_single_coordinate μ S j hj _ (measurable_partialInt μ _ hFm)
  intro η ζ h
  exact partialInt_congr μ _ F h
end Parking
