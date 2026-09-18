import Parking.Support.ProductReveal
import LatticeProb.Prob.Coordinate

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [DecidableEq ι]

/-- A bounded product expectation is the average of its fresh-coordinate sections. -/
theorem integral_coordinate_sections (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Π i, X i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ ω, ‖f ω‖ ≤ B) (j : ι) :
    (∫ ω, f ω ∂(Measure.infinitePi μ)) =
      ∫ ω, ∫ a, f (Function.update ω j a) ∂(μ j) ∂(Measure.infinitePi μ) := by
  let P := Measure.infinitePi μ
  let T : (Π i, X i) × X j → Π i, X i := fun q => Function.update q.1 j q.2
  have hT : MeasurePreserving T (P.prod (μ j)) P := measurePreserving_update_infinitePi μ j
  have hi : Integrable (fun q => f (T q)) (P.prod (μ j)) :=
    Integrable.of_bound (hf.comp hT.measurable).aestronglyMeasurable B (ae_of_all _ fun q => hB (T q))
  have he := integral_map (μ := P.prod (μ j)) (φ := T) (f := f) hT.measurable.aemeasurable
    (by rw [hT.map_eq]; exact hf.aestronglyMeasurable)
  rw [hT.map_eq] at he
  exact he.trans (integral_prod _ hi)

/-- Multiplicative bounds for single reveals accumulate exponentially over a finite set. -/
theorem integral_partial_product_factor (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F G : (Π i, X i) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (B C : ℝ) (hB : 0 ≤ B)
    (hFB : ∀ ω, |F ω| ≤ B) (hGC : ∀ ω, |G ω| ≤ C) (c : ι → ℝ)
    (hsec : ∀ (S : Finset ι) (j : ι), j ∉ S → ∀ ω : Π i, X i,
      (∫ a, partialInt μ (↑(insert j S) : Set ι) F (Function.update ω j a) *
        partialInt μ (↑(insert j S) : Set ι) G (Function.update ω j a) ∂(μ j)) ≤
      Real.exp (c j) * (partialInt μ (↑S : Set ι) F ω * partialInt μ (↑S : Set ι) G ω))
    (S : Finset ι) :
    (∫ ω, partialInt μ (↑S : Set ι) F ω * partialInt μ (↑S : Set ι) G ω
      ∂(Measure.infinitePi μ)) ≤
      Real.exp (∑ j ∈ S, c j) * ((∫ ω, F ω ∂(Measure.infinitePi μ)) * ∫ ω, G ω ∂(Measure.infinitePi μ)) := by
  classical
  let P := Measure.infinitePi μ
  let V (S : Finset ι) (ω : Π i, X i) := partialInt μ (↑S : Set ι) F ω * partialInt μ (↑S : Set ι) G ω
  have hm (S : Finset ι) : Measurable (V S) :=
    (measurable_partialInt μ _ hF).mul (measurable_partialInt μ _ hG)
  have hb (S : Finset ι) (ω : Π i, X i) : ‖V S ω‖ ≤ B * C := by
    change ‖partialInt μ (↑S : Set ι) F ω * partialInt μ (↑S : Set ι) G ω‖ ≤ B * C
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_partialInt_le μ _ F B hFB ω) (abs_partialInt_le μ _ G C hGC ω) (abs_nonneg _) hB
  have hi (S : Finset ι) : Integrable (V S) P :=
    Integrable.of_bound (hm S).aestronglyMeasurable _ (ae_of_all _ fun ω => hb S ω)
  change (∫ ω, V S ω ∂P) ≤ Real.exp (∑ j ∈ S, c j) * ((∫ ω, F ω ∂P) * ∫ ω, G ω ∂P)
  induction S using Finset.induction_on with
  | empty =>
      have he (ω : Π i, X i) : V ∅ ω = (∫ η, F η ∂P) * ∫ η, G η ∂P := by
        have hc (η : Π i, X i) : comb (↑(∅ : Finset ι) : Set ι) ω η = η := by
          funext i
          exact comb_apply_of_notMem (by simp)
        dsimp only [V, partialInt]
        simp only [hc]
        rfl
      simp only [he, integral_const, probReal_univ, one_smul, Finset.sum_empty, Real.exp_zero, one_mul, le_refl]
  | @insert j S hj ih =>
      have hsectioni : Integrable (fun ω => ∫ a, V (insert j S) (Function.update ω j a) ∂(μ j)) P := by
        have hT := measurePreserving_update_infinitePi μ j
        exact (Integrable.of_bound ((hm (insert j S)).comp hT.measurable).aestronglyMeasurable
          (B * C) (ae_of_all _ fun q => hb (insert j S) (Function.update q.1 j q.2))).integral_prod_left
      calc
        (∫ ω, V (insert j S) ω ∂P) = ∫ ω, ∫ a, V (insert j S) (Function.update ω j a) ∂(μ j) ∂P :=
          integral_coordinate_sections μ _ (hm _) (B * C) (hb _) j
        _ ≤ ∫ ω, Real.exp (c j) * V S ω ∂P :=
          integral_mono hsectioni ((hi S).const_mul _) (hsec S j hj)
        _ = Real.exp (c j) * ∫ ω, V S ω ∂P := integral_const_mul _ _
        _ ≤ Real.exp (c j) * (Real.exp (∑ i ∈ S, c i) * ((∫ ω, F ω ∂P) * ∫ ω, G ω ∂P)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (∑ i ∈ insert j S, c i) * ((∫ ω, F ω ∂P) * ∫ ω, G ω ∂P) := by
          rw [Finset.sum_insert hj, Real.exp_add, mul_assoc]

/-- A finite family of reveal factors controls the product of two observables. -/
theorem integral_product_factor (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F G : (Π i, X i) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (B C : ℝ) (hB : 0 ≤ B)
    (hFB : ∀ ω, |F ω| ≤ B) (hGC : ∀ ω, |G ω| ≤ C) (c : ι → ℝ)
    (hsec : ∀ (S : Finset ι) (j : ι), j ∉ S → ∀ ω : Π i, X i,
      (∫ a, partialInt μ (↑(insert j S) : Set ι) F (Function.update ω j a) *
        partialInt μ (↑(insert j S) : Set ι) G (Function.update ω j a) ∂(μ j)) ≤
      Real.exp (c j) * (partialInt μ (↑S : Set ι) F ω * partialInt μ (↑S : Set ι) G ω))
    (S : Finset ι)
    (hFS : ∀ ω η, (∀ i ∈ S, ω i = η i) → F ω = F η)
    (hGS : ∀ ω η, (∀ i ∈ S, ω i = η i) → G ω = G η) :
    (∫ ω, F ω * G ω ∂(Measure.infinitePi μ)) ≤
      Real.exp (∑ j ∈ S, c j) * ((∫ ω, F ω ∂(Measure.infinitePi μ)) * ∫ ω, G ω ∂(Measure.infinitePi μ)) := by
  have h := integral_partial_product_factor μ F G hF hG B C hB hFB hGC c hsec S
  simpa only [partialInt_eq_self μ (↑S : Set ι) F hFS, partialInt_eq_self μ (↑S : Set ι) G hGS] using h
end Parking
