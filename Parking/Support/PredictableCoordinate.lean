/- Bounded predictable products of successively revealed independent coordinates,
with the reward at each step CHOSEN from a finite family by the past.

`Parking.exists_finite_coordinate_moment_bound` bounds the moments of a sum
`∑_j H_j(z) g_j(z_{q j})` in which the reward `g_j` of the fresh coordinate is
fixed in advance.  The directed error field of `parking.tex:3240-3250` is not of
that shape: the instruction `(y,j)` of the directed model contributes the Green
increment at the horizon `n - τ_j(y)`, and `τ_j(y)`, the round at which the
instruction is first used, is determined by the instructions of the layers
strictly below `y` and so is random.  The reward is therefore chosen by the past
out of the finitely many horizons `0, …, N-1`.

The martingale property survives unchanged: writing the selected reward as the
finite sum `∑_M 1{sel_j = M} g_j M` over the family, each summand is a bounded
past-measurable multiple of a fresh centred coordinate, so its conditional mean
is zero; and because at most one indicator fires, the conditional variance is
`H_j^2 ∫ (g_j (sel_j))^2` with no cross terms.
-/
import Parking.Support.CoordinateMartingale

noncomputable section
namespace Parking
open MeasureTheory Finset
open scoped Classical

/-- The moment bound of `Parking.exists_finite_coordinate_moment_bound` when the
reward of the fresh coordinate is selected out of a finite family by a
past-measurable rule. -/
theorem exists_finite_coordinate_moment_bound_sel (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω ι : Type) (X : ι → Type)
      (_ : MeasurableSpace Ω) (_ : DecidableEq ι) (_ : ∀ i, MeasurableSpace (X i))
      (K N : ℕ) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (P : ∀ i, Measure (X i)) (_ : ∀ i, IsProbabilityMeasure (P i))
      (b : Π i, X i) (q : Fin K → ι), Function.Injective q →
      ∀ (H : Fin K → Ω × (Π i, X i) → ℝ) (sel : Fin K → Ω × (Π i, X i) → Fin N)
        (g : ∀ j : Fin K, Fin N → X (q j) → ℝ) (r a : ℝ),
      (∀ j, Measurable[coordinateFiltration b q j.val] (H j)) →
      (∀ j, Measurable[coordinateFiltration b q j.val] (sel j)) →
      (∀ j z, |H j z| ≤ 1) → (∀ j M, Measurable (g j M)) → (∀ j M z, |g j M z| ≤ a) →
      (∀ j M, ∫ z, g j M z ∂(P (q j)) = 0) → 2 ≤ r → 0 < a →
      (∫ z, |∑ j : Fin K, H j z * g j (sel j z) (z.2 (q j))| ^ r
          ∂(μ.prod (Measure.infinitePi P))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ z, (∑ j : Fin K,
              H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(P (q j))) ^ (r / 2)
          ∂(μ.prod (Measure.infinitePi P))) ^ (1 / r) + r * a) := by
  obtain ⟨C, hC, hb⟩ := exists_bernstein_range_bound hBern
  refine ⟨C, hC, fun Ω ι X _ _ _ K N μ _ P _ b q hq H sel g r a hH hsel hHb hg hgb hg0 hr ha => ?_⟩
  let Q := μ.prod (Measure.infinitePi P)
  let F := coordinateFiltration (Ω := Ω) b q
  let H' : Fin K → Fin N → Ω × (Π i, X i) → ℝ := fun j M z => if sel j z = M then H j z else 0
  let A : Fin K → Ω × (Π i, X i) → ℝ := fun j z => H j z * g j (sel j z) (z.2 (q j))
  have hH'm (j : Fin K) (M : Fin N) : Measurable[F j.val] (H' j M) := by
    refine Measurable.ite ?_ (hH j) measurable_const
    exact (hsel j) (measurableSet_singleton M)
  have hH'b (j : Fin K) (M : Fin N) (z : Ω × (Π i, X i)) : |H' j M z| ≤ 1 := by
    dsimp only [H']; split_ifs
    · exact hHb j z
    · simp
  have hone (j : Fin K) (z : Ω × (Π i, X i)) (φ : Fin N → ℝ) :
      (∑ M : Fin N, (if sel j z = M then (1 : ℝ) else 0) * φ M) = φ (sel j z) := by
    rw [Finset.sum_eq_single (sel j z)]
    · simp
    · intro M _ hM; simp [Ne.symm hM]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsum (j : Fin K) (z : Ω × (Π i, X i)) :
      (∑ M : Fin N, H' j M z * g j M (z.2 (q j))) = A j z := by
    have he : ∀ M : Fin N, H' j M z * g j M (z.2 (q j))
        = (if sel j z = M then (1 : ℝ) else 0) * (H j z * g j M (z.2 (q j))) := by
      intro M; dsimp only [H']; split_ifs <;> ring
    simp only [he]
    rw [hone j z (fun M => H j z * g j M (z.2 (q j)))]
  have hsqs (j : Fin K) (z : Ω × (Π i, X i)) :
      (∑ M : Fin N, H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2) = A j z ^ 2 := by
    have he : ∀ M : Fin N, H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2
        = (if sel j z = M then (1 : ℝ) else 0) * (H j z ^ 2 * g j M (z.2 (q j)) ^ 2) := by
      intro M; dsimp only [H']; split_ifs <;> ring
    simp only [he]
    rw [hone j z (fun M => H j z ^ 2 * g j M (z.2 (q j)) ^ 2)]
    dsimp only [A]; ring
  have hvar (j : Fin K) (z : Ω × (Π i, X i)) :
      (∑ M : Fin N, H' j M z ^ 2 * ∫ x, g j M x ^ 2 ∂(P (q j)))
        = H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(P (q j)) := by
    have he : ∀ M : Fin N, H' j M z ^ 2 * (∫ x, g j M x ^ 2 ∂(P (q j)))
        = (if sel j z = M then (1 : ℝ) else 0) * (H j z ^ 2 * ∫ x, g j M x ^ 2 ∂(P (q j))) := by
      intro M; dsimp only [H']; split_ifs <;> ring
    simp only [he]
    rw [hone j z (fun M => H j z ^ 2 * ∫ x, g j M x ^ 2 ∂(P (q j)))]
  have hAb (j : Fin K) (z : Ω × (Π i, X i)) : |A j z| ≤ a := by
    change |H j z * g j (sel j z) (z.2 (q j))| ≤ a
    rw [abs_mul]
    exact (mul_le_mul (hHb j z) (hgb j _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul a)
  have hterm_m (j : Fin K) (M : Fin N) :
      Measurable[F (j.val + 1)] fun z => H' j M z * g j M (z.2 (q j)) := by
    apply ((hH'm j M).mono (coordinateFiltration_mono b q (Nat.le_succ j.val)) le_rfl).mul
    exact (hg j M).comp (measurable_coordinateFiltration_eval b hq j (Nat.lt_succ_self j.val))
  have hAm (j : Fin K) : Measurable[F (j.val + 1)] (A j) := by
    have he : A j = fun z => ∑ M : Fin N, H' j M z * g j M (z.2 (q j)) := by
      funext z; exact (hsum j z).symm
    rw [he]
    exact Finset.measurable_sum _ fun M _ => hterm_m j M
  have hAi (j : Fin K) : Integrable (A j) Q :=
    Integrable.of_bound ((hAm j).mono (coordinateFiltration_le b q (j.val + 1)) le_rfl).aestronglyMeasurable a
      (ae_of_all Q fun z => by simpa only [Real.norm_eq_abs] using hAb j z)
  have hH'i (j : Fin K) (M : Fin N) : Integrable (H' j M) Q :=
    Integrable.of_bound ((hH'm j M).mono (coordinateFiltration_le b q j.val) le_rfl).aestronglyMeasurable 1
      (ae_of_all Q fun z => by simpa only [Real.norm_eq_abs] using hH'b j M z)
  have hH'2i (j : Fin K) (M : Fin N) : Integrable (fun z => H' j M z ^ 2) Q :=
    Integrable.of_bound (((hH'm j M).mono (coordinateFiltration_le b q j.val) le_rfl).pow_const 2).aestronglyMeasurable 1
      (ae_of_all Q fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg (H' j M z)) (hH'b j M z) 2)
  have htermi (j : Fin K) (M : Fin N) :
      Integrable (fun z => H' j M z * g j M (z.2 (q j))) Q :=
    Integrable.of_bound ((hterm_m j M).mono (coordinateFiltration_le b q (j.val + 1)) le_rfl).aestronglyMeasurable a
      (ae_of_all Q fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul (hH'b j M z) (hgb j M _) (abs_nonneg _) zero_le_one).trans_eq (one_mul a))
  have hterm2m (j : Fin K) (M : Fin N) :
      Measurable[F (j.val + 1)] fun z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 := by
    apply (((hH'm j M).mono (coordinateFiltration_mono b q (Nat.le_succ j.val)) le_rfl).pow_const 2).mul
    exact ((hg j M).pow_const 2).comp
      (measurable_coordinateFiltration_eval b hq j (Nat.lt_succ_self j.val))
  have hterm2i (j : Fin K) (M : Fin N) :
      Integrable (fun z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2) Q := by
    refine Integrable.of_bound
      ((hterm2m j M).mono (coordinateFiltration_le b q (j.val + 1)) le_rfl).aestronglyMeasurable
      (a ^ 2) ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
    have h1 : |H' j M z| ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (abs_nonneg (H' j M z)) (hH'b j M z) 2
    have h2 : |g j M (z.2 (q j))| ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hgb j M _) 2
    calc |H' j M z| ^ 2 * |g j M (z.2 (q j))| ^ 2 ≤ 1 * (a ^ 2) :=
          mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = a ^ 2 := one_mul _
  have hAc (j : Fin K) : Q[A j | F j.val] =ᵐ[Q] 0 := by
    have he : A j = fun z => ∑ M : Fin N, H' j M z * g j M (z.2 (q j)) := by
      funext z; exact (hsum j z).symm
    have hfs : Q[fun z => ∑ M : Fin N, H' j M z * g j M (z.2 (q j)) | F j.val]
        =ᵐ[Q] fun z => ∑ M : Fin N,
          (Q[fun z => H' j M z * g j M (z.2 (q j)) | F j.val]) z := by
      have h := condExp_finsetSum (μ := Q) (m := F j.val)
        (s := (Finset.univ : Finset (Fin N)))
        (f := fun M z => H' j M z * g j M (z.2 (q j))) (fun M _ => htermi j M)
      have hpi : (∑ M : Fin N, fun z => H' j M z * g j M (z.2 (q j)))
          = fun z => ∑ M : Fin N, H' j M z * g j M (z.2 (q j)) := by
        funext z; simp
      rw [hpi] at h
      filter_upwards [h] with z hz
      rw [hz]; simp
    have heach (M : Fin N) : Q[fun z => H' j M z * g j M (z.2 (q j)) | F j.val] =ᵐ[Q] 0 := by
      have h := condExp_mul_fresh_coordinate μ P (q j) (b (q j)) (F j.val)
        (coordinateFiltration_le b q j.val)
        (fun S hS η σ => coordinateFiltration_set_update b q j le_rfl _ S hS η σ)
        (H' j M) (hH'm j M) (hH'i j M) (g j M) (hg j M) (htermi j M)
      filter_upwards [h] with z hz
      simpa only [Q, hg0 j M, mul_zero, Pi.zero_apply] using hz
    rw [he]
    filter_upwards [hfs, ae_all_iff.2 heach] with z hz hz2
    rw [hz]
    simp only [Pi.zero_apply] at hz2 ⊢
    exact Finset.sum_eq_zero fun M _ => hz2 M
  have hAv (j : Fin K) : Q[fun z => A j z ^ 2 | F j.val] =ᵐ[Q]
      fun z => H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(P (q j)) := by
    have he : (fun z => A j z ^ 2)
        = fun z => ∑ M : Fin N, H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 := by
      funext z; exact (hsqs j z).symm
    have hfs : Q[fun z => ∑ M : Fin N, H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 | F j.val]
        =ᵐ[Q] fun z => ∑ M : Fin N,
          (Q[fun z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 | F j.val]) z := by
      have h := condExp_finsetSum (μ := Q) (m := F j.val)
        (s := (Finset.univ : Finset (Fin N)))
        (f := fun M z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2) (fun M _ => hterm2i j M)
      have hpi : (∑ M : Fin N, fun z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2)
          = fun z => ∑ M : Fin N, H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 := by
        funext z; simp
      rw [hpi] at h
      filter_upwards [h] with z hz
      rw [hz]; simp
    have heach (M : Fin N) : Q[fun z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 | F j.val]
        =ᵐ[Q] fun z => H' j M z ^ 2 * ∫ x, g j M x ^ 2 ∂(P (q j)) := by
      exact condExp_mul_fresh_coordinate μ P (q j) (b (q j)) (F j.val)
        (coordinateFiltration_le b q j.val)
        (fun S hS η σ => coordinateFiltration_set_update b q j le_rfl _ S hS η σ)
        (fun z => H' j M z ^ 2) ((hH'm j M).pow_const 2) (hH'2i j M)
        (fun x => g j M x ^ 2) ((hg j M).pow_const 2) (hterm2i j M)
    rw [he]
    filter_upwards [hfs, ae_all_iff.2 heach] with z hz hz2
    rw [hz]
    rw [show (∑ M : Fin N, (Q[fun z => H' j M z ^ 2 * g j M (z.2 (q j)) ^ 2 | F j.val]) z)
        = ∑ M : Fin N, H' j M z ^ 2 * ∫ x, g j M x ^ 2 ∂(P (q j)) from
      Finset.sum_congr rfl fun M _ => hz2 M]
    exact hvar j z
  let ξ : ℕ → Ω × (Π i, X i) → ℝ := fun i => if hi : i < K then A ⟨i, hi⟩ else fun _ => 0
  let v : ℕ → Ω × (Π i, X i) → ℝ := fun i => if hi : i < K then
    fun z => H ⟨i, hi⟩ z ^ 2 * ∫ x, g ⟨i, hi⟩ (sel ⟨i, hi⟩ z) x ^ 2 ∂(P (q ⟨i, hi⟩)) else fun _ => 0
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
      ∑ j : Fin K, H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(P (q j)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => by simp only [v, dif_pos j.isLt]
  simpa only [heA, hev] using h

end Parking
end
