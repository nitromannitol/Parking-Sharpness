/-
Fresh independent layers and the sum of nonnegative rewards paid by a potential.
-/
import Parking.Support.LayerHitting

noncomputable section
open MeasureTheory LatticeProb

variable {α : Type*} [MeasurableSpace α]

/-- A bound on fresh-layer sections passes to the product expectation. -/
theorem Parking.integral_le_of_bounded_layer_sections (μ : Measure α) [IsProbabilityMeasure μ]
    (f g : (ℕ → α) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hfB : ∀ ω, ‖f ω‖ ≤ B) (hgC : ∀ ω, ‖g ω‖ ≤ C) (n : ℕ)
    (hsec : ∀ ω, ∫ v, f (Function.update ω n v) ∂μ ≤ g ω) :
    ∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫ ω, g ω ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  let P := Measure.infinitePi fun _ : ℕ => μ
  let T : (ℕ → α) × α → ℕ → α := fun q => Function.update q.1 n q.2
  have hT : MeasurePreserving T (P.prod μ) P :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : ℕ => μ) n
  have hint : Integrable (fun q => f (T q)) (P.prod μ) :=
    Integrable.of_bound ((hf.comp hT.measurable).aestronglyMeasurable) B
      (Filter.Eventually.of_forall fun q => hfB (T q))
  have hgint : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall hgC)
  have heq := integral_map (μ := P.prod μ) (φ := T) (f := f) hT.measurable.aemeasurable
    (by rw [hT.map_eq]; exact hf.aestronglyMeasurable)
  rw [hT.map_eq] at heq
  calc
    ∫ ω, f ω ∂P = ∫ q, f (T q) ∂(P.prod μ) := heq
    _ = ∫ ω, ∫ v, f (Function.update ω n v) ∂μ ∂P := integral_prod _ hint
    _ ≤ ∫ ω, g ω ∂P := integral_mono hint.integral_prod_left hgint hsec

/-- A bounded nonnegative potential pays for the sum of its one-round expected decrements. -/
theorem Parking.layer_reward_sum_le (μ : Measure α) [IsProbabilityMeasure μ]
    (V r : (ℕ → α) → ℕ → ℝ) (hV : ∀ n, Measurable fun ω => V ω n)
    (hr : ∀ n, Measurable fun ω => r ω n) (B : ℝ)
    (hVB : ∀ ω n, 0 ≤ V ω n ∧ V ω n ≤ B)
    (hrB : ∀ ω n, 0 ≤ r ω n ∧ r ω n ≤ 1)
    (hsec : ∀ ω n, ∫ v, V (Function.update ω n v) (n + 1) ∂μ ≤ V ω n - r ω n)
    (a : ℝ) (h0 : ∀ ω, V ω 0 = a) (T : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range T, r ω n ∂(Measure.infinitePi fun _ : ℕ => μ) ≤ a := by
  let P := Measure.infinitePi fun _ : ℕ => μ
  have hVi (n : ℕ) : Integrable (fun ω => V ω n) P :=
    Integrable.of_bound (hV n).aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hVB ω n).1]; exact (hVB ω n).2)
  have hri (n : ℕ) : Integrable (fun ω => r ω n) P :=
    Integrable.of_bound (hr n).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrB ω n).1]; exact (hrB ω n).2)
  have hstep (n : ℕ) : (∫ ω, V ω (n + 1) ∂P) ≤ (∫ ω, V ω n ∂P) - ∫ ω, r ω n ∂P := by
    rw [← integral_sub (hVi n) (hri n)]
    apply Parking.integral_le_of_bounded_layer_sections μ _ _ (hV (n + 1)) ((hV n).sub (hr n))
      B (B + 1) _ _ n (fun ω => hsec ω n)
    · intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hVB ω (n + 1)).1]
      exact (hVB ω (n + 1)).2
    · intro ω
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg (hVB ω n).1, abs_of_nonneg (hrB ω n).1]
        exact add_le_add (hVB ω n).2 (hrB ω n).2)
  have hsum : ∀ N : ℕ, (∫ ω, V ω N ∂P) + ∑ n ∈ Finset.range N, ∫ ω, r ω n ∂P ≤ a := by
    intro N
    induction N with
    | zero => simp [h0]
    | succ N ih => rw [Finset.sum_range_succ]; linarith only [ih, hstep N]
  rw [integral_finsetSum _ (fun n _ => hri n)]
  exact (le_add_of_nonneg_left (integral_nonneg fun ω => (hVB ω T).1)).trans (hsum T)
