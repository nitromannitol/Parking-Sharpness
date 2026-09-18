import Parking.Support.ProductConditioning

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Partial integration fixes a functional that already reads only retained coordinates. -/
theorem partialInt_eq_self (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] (F : (Π i, X i) → ℝ)
    (hF : ∀ ω η, (∀ i ∈ S, ω i = η i) → F ω = F η) (ω : Π i, X i) :
    partialInt μ S F ω = F ω := by
  unfold partialInt
  have he (η : Π i, X i) : F (comb S ω η) = F ω :=
    hF _ _ (fun i hi => comb_apply_of_mem hi)
  simp only [he, integral_const, probReal_univ, one_smul]

/-- A functional of the retained coordinates and one fresh coordinate is averaged in that coordinate alone. -/
theorem partialInt_single_coordinate [DecidableEq ι]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] (j : ι) (hj : j ∉ S)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F)
    (hF : ∀ ω η, (∀ i ∈ insert j S, ω i = η i) → F ω = F η) (ω : Π i, X i) :
    partialInt μ S F ω = ∫ a, F (Function.update ω j a) ∂(μ j) := by
  have he (η : Π i, X i) : F (comb S ω η) = F (Function.update ω j (η j)) := by
    apply hF
    intro i hi
    rcases hi with rfl | hi
    · rw [comb_apply_of_notMem hj, Function.update_self]
    · have hij : i ≠ j := fun he => hj (he ▸ hi)
      rw [comb_apply_of_mem hi, Function.update_of_ne hij]
  have hm : Measurable (fun a : X j => F (Function.update ω j a)) := by
    apply hFm.comp
    exact measurable_update ω
  change (∫ η, F (comb S ω η) ∂(Measure.infinitePi μ)) = _
  simp only [he]
  have hp := measurePreserving_eval_infinitePi μ j
  rw [← integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable, hp.map_eq]

/-- A bounded functional has equally bounded partial integrals, at every retained configuration. -/
theorem abs_partialInt_le (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] (F : (Π i, X i) → ℝ) (B : ℝ)
    (hB : ∀ ω, |F ω| ≤ B) (ω : Π i, X i) : |partialInt μ S F ω| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.infinitePi μ)
    (f := fun η => F (comb S ω η)) (ae_of_all _ fun η => hB (comb S ω η))
  simpa only [partialInt, Real.norm_eq_abs, probReal_univ, mul_one] using h
end Parking
