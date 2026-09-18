/- Bounded predictable products of successively revealed independent coordinates. -/
import Parking.Support.CoordinateFiltration
import Parking.Support.CoordinateConditional
import Parking.Support.BernsteinRange

noncomputable section
namespace Parking
open MeasureTheory Finset
open scoped Classical

theorem exists_finite_coordinate_moment_bound (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω ι : Type) (X : ι → Type)
      (_ : MeasurableSpace Ω) (_ : DecidableEq ι) (_ : ∀ i, MeasurableSpace (X i))
      (K : ℕ) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (P : ∀ i, Measure (X i)) (_ : ∀ i, IsProbabilityMeasure (P i))
      (b : Π i, X i) (q : Fin K → ι), Function.Injective q →
      ∀ (H : Fin K → Ω × (Π i, X i) → ℝ) (g : ∀ j, X (q j) → ℝ) (r a : ℝ),
      (∀ j, Measurable[coordinateFiltration b q j.val] (H j)) →
      (∀ j z, |H j z| ≤ 1) → (∀ j, Measurable (g j)) → (∀ j z, |g j z| ≤ a) →
      (∀ j, ∫ z, g j z ∂(P (q j)) = 0) → 2 ≤ r → 0 < a →
      (∫ z, |∑ j : Fin K, H j z * g j (z.2 (q j))| ^ r ∂(μ.prod (Measure.infinitePi P))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ z, (∑ j : Fin K, H j z ^ 2 * ∫ x, g j x ^ 2 ∂(P (q j))) ^ (r / 2)
          ∂(μ.prod (Measure.infinitePi P))) ^ (1 / r) + r * a) := by
  obtain ⟨C, hC, hb⟩ := exists_bernstein_range_bound hBern
  refine ⟨C, hC, fun Ω ι X _ _ _ K μ _ P _ b q hq H g r a hH hHb hg hgb hg0 hr ha => ?_⟩
  let Q := μ.prod (Measure.infinitePi P)
  let F := coordinateFiltration (Ω := Ω) b q
  let A : Fin K → Ω × (Π i, X i) → ℝ := fun j z => H j z * g j (z.2 (q j))
  have hHm (j : Fin K) : Measurable (H j) := (hH j).mono (coordinateFiltration_le b q j.val) le_rfl
  have hHi (j : Fin K) : Integrable (H j) Q :=
    Integrable.of_bound (hHm j).aestronglyMeasurable 1
      (ae_of_all Q fun z => by simpa only [Real.norm_eq_abs] using hHb j z)
  have hAm (j : Fin K) : Measurable[F (j.val + 1)] (A j) := by
    apply ((hH j).mono (coordinateFiltration_mono b q (Nat.le_succ j.val)) le_rfl).mul
    exact (hg j).comp (measurable_coordinateFiltration_eval b hq j (Nat.lt_succ_self j.val))
  have hAb (j : Fin K) (z : Ω × (Π i, X i)) : |A j z| ≤ a := by
    change |H j z * g j (z.2 (q j))| ≤ a
    rw [abs_mul]
    exact (mul_le_mul (hHb j z) (hgb j _) (abs_nonneg _) zero_le_one).trans_eq (one_mul a)
  have hAi (j : Fin K) : Integrable (A j) Q :=
    Integrable.of_bound ((hAm j).mono (coordinateFiltration_le b q (j.val + 1)) le_rfl).aestronglyMeasurable a
      (ae_of_all Q fun z => by simpa only [Real.norm_eq_abs] using hAb j z)
  have hAc (j : Fin K) : Q[A j | F j.val] =ᵐ[Q] 0 := by
    have h := condExp_mul_fresh_coordinate μ P (q j) (b (q j)) (F j.val)
      (coordinateFiltration_le b q j.val)
      (fun S hS η σ => coordinateFiltration_set_update b q j le_rfl _ S hS η σ)
      (H j) (hH j) (hHi j) (g j) (hg j) (hAi j)
    filter_upwards [h] with z hz
    simpa only [Q, A, hg0 j, mul_zero, Pi.zero_apply] using hz
  have hH2i (j : Fin K) : Integrable (fun z => H j z ^ 2) Q := by
    apply Integrable.of_bound (hHm j |>.pow_const 2 |>.aestronglyMeasurable) 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg (H j z)) (hHb j z) 2
    simpa only [one_pow] using h
  have hA2i (j : Fin K) : Integrable (fun z => A j z ^ 2) Q := by
    apply Integrable.of_bound (((hAm j).mono (coordinateFiltration_le b q (j.val + 1)) le_rfl).pow_const 2).aestronglyMeasurable (a ^ 2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg (A j z)) (hAb j z) 2
  have hAv (j : Fin K) : Q[fun z => A j z ^ 2 | F j.val] =ᵐ[Q]
      fun z => H j z ^ 2 * ∫ x, g j x ^ 2 ∂(P (q j)) := by
    have he : (fun z => A j z ^ 2) = fun z => H j z ^ 2 * g j (z.2 (q j)) ^ 2 := by
      funext z
      exact mul_pow _ _ _
    have h := condExp_mul_fresh_coordinate μ P (q j) (b (q j)) (F j.val)
      (coordinateFiltration_le b q j.val)
      (fun S hS η σ => coordinateFiltration_set_update b q j le_rfl _ S hS η σ)
      (fun z => H j z ^ 2) ((hH j).pow_const 2) (hH2i j)
      (fun x => g j x ^ 2) ((hg j).pow_const 2) (he ▸ hA2i j)
    rw [he]
    exact h
  let ξ : ℕ → Ω × (Π i, X i) → ℝ := fun i => if hi : i < K then A ⟨i, hi⟩ else fun _ => 0
  let v : ℕ → Ω × (Π i, X i) → ℝ := fun i => if hi : i < K then
    fun z => H ⟨i, hi⟩ z ^ 2 * ∫ x, g ⟨i, hi⟩ x ^ 2 ∂(P (q ⟨i, hi⟩)) else fun _ => 0
  have hξm (i : ℕ) : Measurable[F (i + 1)] (ξ i) := by
    by_cases hi : i < K
    · simpa only [ξ, dif_pos hi] using hAm ⟨i, hi⟩
    · simp only [ξ, dif_neg hi]; exact measurable_const
  have hξi (i : ℕ) : Integrable (ξ i) Q := by
    by_cases hi : i < K
    · simpa only [ξ, dif_pos hi] using hAi ⟨i, hi⟩
    · simp only [ξ, dif_neg hi]; exact integrable_zero _ _ _
  have hξc (i : ℕ) (hi : i < K) : Q[ξ i | F i] =ᵐ[Q] 0 := by
    simpa only [ξ, dif_pos hi] using hAc ⟨i, hi⟩
  have hξv (i : ℕ) (hi : i < K) : Q[fun z => ξ i z ^ 2 | F i] =ᵐ[Q] v i := by
    simpa only [ξ, v, dif_pos hi] using hAv ⟨i, hi⟩
  have hξb (i : ℕ) (hi : i < K) (z : Ω × (Π i, X i)) : |ξ i z| ≤ a := by
    simpa only [ξ, dif_pos hi] using hAb ⟨i, hi⟩ z
  have h := hb (Ω × (Π i, X i)) inferInstance Q inferInstance K F ξ v r a
    (coordinateFiltration_mono b q) (coordinateFiltration_le b q) hξm hξi hξc hξv hr ha hξb
  have heA (z : Ω × (Π i, X i)) : (∑ i ∈ range K, ξ i z) = ∑ j : Fin K, A j z := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => by simp only [ξ, dif_pos j.isLt]
  have hev (z : Ω × (Π i, X i)) : (∑ i ∈ range K, v i z) =
      ∑ j : Fin K, H j z ^ 2 * ∫ x, g j x ^ 2 ∂(P (q j)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => by simp only [v, dif_pos j.isLt]
  simpa only [heA, hev] using h

end Parking
