import Parking.Support.PartialInvariant

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [DecidableEq ι]

/-- Updating a functional before partial integration retains that coordinate at the prescribed value. -/
theorem partialInt_update_insert (μ : ∀ i, Measure (X i))
    (S : Set ι) [DecidablePred (· ∈ S)] (F : (Π i, X i) → ℝ) (j : ι)
    (ω : Π i, X i) (a : X j) :
    partialInt μ S (fun η => F (Function.update η j a)) ω =
      partialInt μ (insert j S) F (Function.update ω j a) := by
  unfold partialInt
  apply integral_congr_ae
  apply ae_of_all
  intro η
  apply congrArg F
  funext i
  by_cases hi : i = j
  · subst i; simp [comb]
  · simp [comb, hi]

omit [DecidableEq ι] in
/-- Pointwise linear comparisons survive partial integration at every retained configuration. -/
theorem partialInt_mul_le (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] (F G : (Π i, X i) → ℝ)
    (hF : Measurable F) (hG : Measurable G) (B C : ℝ)
    (hFB : ∀ η, |F η| ≤ B) (hGC : ∀ η, |G η| ≤ C) (c : ℝ) (hc : ∀ η, c * F η ≤ G η)
    (ω : Π i, X i) : c * partialInt μ S F ω ≤ partialInt μ S G ω := by
  have hm : Measurable (fun η : Π i, X i => comb S ω η) :=
    (measurable_comb S).comp (measurable_const.prodMk measurable_id)
  have hFi : Integrable (fun η => F (comb S ω η)) (Measure.infinitePi μ) :=
    Integrable.of_bound (hF.comp hm).aestronglyMeasurable B
      (ae_of_all _ fun η => hFB (comb S ω η))
  have hGi : Integrable (fun η => G (comb S ω η)) (Measure.infinitePi μ) :=
    Integrable.of_bound (hG.comp hm).aestronglyMeasurable C
      (ae_of_all _ fun η => hGC (comb S ω η))
  unfold partialInt
  rw [← integral_const_mul]
  exact integral_mono (hFi.const_mul c) hGi (fun η => hc (comb S ω η))
end Parking
