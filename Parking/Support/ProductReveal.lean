import Parking.Support.ProductTower
import Parking.Support.CenteredVariance

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [DecidableEq ι]

/-- Resampling an omitted coordinate leaves a partial integral unchanged. -/
theorem partialInt_update_of_notMem (μ : ∀ i, Measure (X i))
    (S : Set ι) [DecidablePred (· ∈ S)] (F : (Π i, X i) → ℝ)
    (j : ι) (hj : j ∉ S) (ω : Π i, X i) (a : X j) :
    partialInt μ S F (Function.update ω j a) = partialInt μ S F ω := by
  apply partialInt_congr
  intro i hi
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  rw [Function.update_of_ne hij]

/-- The reveal difference is its fresh-coordinate section minus that section's average. -/
theorem partialInt_reveal_eq_centered (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set ι) [DecidablePred (· ∈ S)] (j : ι) (hj : j ∉ S)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F) (B : ℝ) (hB : ∀ ω, |F ω| ≤ B)
    (ω : Π i, X i) (a : X j) :
    partialInt μ (insert j S) F (Function.update ω j a) -
      partialInt μ S F (Function.update ω j a) =
    partialInt μ (insert j S) F (Function.update ω j a) -
      ∫ b, partialInt μ (insert j S) F (Function.update ω j b) ∂(μ j) := by
  rw [partialInt_update_of_notMem μ S F j hj,
    partialInt_insert_coordinate μ S j hj F hFm B hB]

/-- Bounds on fresh-coordinate sections give the predictable variance bound for a reveal. -/
theorem partialInt_reveal_bounds (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (base : Π i, X i) (S : Set ι) [DecidablePred (· ∈ S)] (j : ι) (hj : j ∉ S)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F) (B : ℝ) (hB : ∀ ω, |F ω| ≤ B)
    (a : ℝ) (V : (Π i, X i) → ℝ)
    (hsec : ∀ ω, let f := fun b => partialInt μ (insert j S) F (Function.update ω j b)
      (∀ b, |f b - ∫ c, f c ∂(μ j)| ≤ a) ∧
        (∫ b, (f b - ∫ c, f c ∂(μ j)) ^ 2 ∂(μ j)) ≤ V ω) :
    (∀ ω, |partialInt μ (insert j S) F ω - partialInt μ S F ω| ≤ a) ∧
    ((Measure.infinitePi μ)[fun ω => (partialInt μ (insert j S) F ω - partialInt μ S F ω) ^ 2 |
      productCoordAlg base S] ≤ᵐ[Measure.infinitePi μ] V) := by
  let D : (Π i, X i) → ℝ := fun ω => partialInt μ (insert j S) F ω - partialInt μ S F ω
  have hD : Measurable D := (measurable_partialInt μ _ hFm).sub (measurable_partialInt μ _ hFm)
  have hDa (ω : Π i, X i) : |D ω| ≤ a := by
    have h := (hsec ω).1 (ω j)
    rw [← partialInt_reveal_eq_centered μ S j hj F hFm B hB] at h
    simpa only [Function.update_eq_self] using h
  refine ⟨hDa, ?_⟩
  have hDi : Integrable (fun ω => D ω ^ 2) (Measure.infinitePi μ) :=
    Integrable.of_bound (hD.pow_const 2).aestronglyMeasurable (a ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hDa ω))).mpr (hDa ω))
  have hcond := partialInt_eq_condExp_coord μ base S (hD.pow_const 2) hDi
  filter_upwards [hcond] with ω hω
  rw [← hω]
  have hdep : ∀ η ζ, (∀ i ∈ insert j S, η i = ζ i) → D η ^ 2 = D ζ ^ 2 := by
    intro η ζ h
    dsimp only [D]
    rw [partialInt_congr μ (insert j S) F h,
      partialInt_congr μ S F (fun i hi => h i (Set.mem_insert_of_mem j hi))]
  rw [partialInt_single_coordinate μ S j hj _ (hD.pow_const 2) hdep ω]
  simp_rw [D, partialInt_reveal_eq_centered μ S j hj F hFm B hB]
  exact (hsec ω).2
end Parking
