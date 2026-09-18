import Parking.Support.ProductConditioning

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Retaining more coordinates enlarges the generated sigma algebra. -/
theorem productCoordAlg_mono (b : Π i, X i) (S T : Set ι)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (hST : S ⊆ T) :
    productCoordAlg b S ≤ productCoordAlg b T := by
  have he : (fun ω : Π i, X i => comb S ω b) =
      (fun ω => comb S ω b) ∘ (fun ω => comb T ω b) := by
    funext ω i
    by_cases hi : i ∈ S
    · simp [comb, hi, hST hi]
    · simp [comb, hi]
  have hm : Measurable[productCoordAlg b T] (fun ω : Π i, X i => comb S ω b) := by
    rw [he]
    exact (measurable_coordTruncate b S).comp (Measurable.of_comap_le le_rfl)
  exact hm.comap_le

/-- Successive partial integrals form the conditional-expectation martingale. -/
theorem condExp_partialInt_of_subset (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (b : Π i, X i) (S T : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hST : S ⊆ T) {F : (Π i, X i) → ℝ} (hFm : Measurable F)
    (hFi : Integrable F (Measure.infinitePi μ)) :
    (Measure.infinitePi μ)[partialInt μ T F | productCoordAlg b S] =ᵐ[Measure.infinitePi μ]
      partialInt μ S F := by
  exact (condExp_congr_ae (partialInt_eq_condExp_coord μ b T hFm hFi)).trans
    ((condExp_condExp_of_le (productCoordAlg_mono b S T hST) (productCoordAlg_le b T)).trans
      (partialInt_eq_condExp_coord μ b S hFm hFi).symm)

/-- The increments of the coordinate-reveal martingale. -/
def productDoobDiff (μ : ∀ i, Measure (X i)) (S : ℕ → Set ι)
    [∀ n, DecidablePred (· ∈ S n)] (F : (Π i, X i) → ℝ) (n : ℕ) : (Π i, X i) → ℝ :=
  fun ω => partialInt μ (S n) F ω - partialInt μ (S (n - 1)) F ω

/-- Every reveal increment is measurable after its reveal. -/
theorem measurable_productDoobDiff (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (b : Π i, X i) (S : ℕ → Set ι) [∀ n, DecidablePred (· ∈ S n)] (hS : Monotone S)
    {F : (Π i, X i) → ℝ} (hFm : Measurable F) (n : ℕ) :
    Measurable[productCoordAlg b (S n)] (productDoobDiff μ S F n) :=
  (measurable_partialInt_coord μ b (S n) hFm).sub
    ((measurable_partialInt_coord μ b (S (n - 1)) hFm).mono
      (productCoordAlg_mono b _ _ (hS (Nat.sub_le n 1))) le_rfl)

/-- Reveal increments are integrable. -/
theorem integrable_productDoobDiff (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : ℕ → Set ι) [∀ n, DecidablePred (· ∈ S n)] {F : (Π i, X i) → ℝ}
    (hFi : Integrable F (Measure.infinitePi μ)) (n : ℕ) :
    Integrable (productDoobDiff μ S F n) (Measure.infinitePi μ) :=
  (integrable_partialInt μ _ hFi).sub (integrable_partialInt μ _ hFi)

/-- Each reveal increment has conditional mean zero. -/
theorem condExp_productDoobDiff (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (b : Π i, X i) (S : ℕ → Set ι) [∀ n, DecidablePred (· ∈ S n)] (hS : Monotone S)
    {F : (Π i, X i) → ℝ} (hFm : Measurable F) (hFi : Integrable F (Measure.infinitePi μ)) (n : ℕ) :
    (Measure.infinitePi μ)[productDoobDiff μ S F n | productCoordAlg b (S (n - 1))] =ᵐ[Measure.infinitePi μ] 0 := by
  change (Measure.infinitePi μ)[partialInt μ (S n) F - partialInt μ (S (n - 1)) F |
    productCoordAlg b (S (n - 1))] =ᵐ[Measure.infinitePi μ] 0
  have h := condExp_sub (integrable_partialInt μ (S n) hFi)
    (integrable_partialInt μ (S (n - 1)) hFi) (productCoordAlg b (S (n - 1)))
  have h₁ := condExp_partialInt_of_subset μ b (S (n - 1)) (S n) (hS (Nat.sub_le n 1)) hFm hFi
  have h₂ := condExp_partialInt_of_subset μ b (S (n - 1)) (S (n - 1)) (Set.Subset.refl _) hFm hFi
  simpa only [sub_self] using h.trans (h₁.sub h₂)

/-- The finite sum of reveal increments telescopes exactly. -/
theorem sum_productDoobDiff (μ : ∀ i, Measure (X i)) (S : ℕ → Set ι)
    [∀ n, DecidablePred (· ∈ S n)] (F : (Π i, X i) → ℝ) (k : ℕ) (ω : Π i, X i) :
    ∑ n ∈ Finset.Icc 1 k, productDoobDiff μ S F n ω =
      partialInt μ (S k) F ω - partialInt μ (S 0) F ω := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
      simp only [productDoobDiff, Nat.add_sub_cancel]
      ring
end Parking
