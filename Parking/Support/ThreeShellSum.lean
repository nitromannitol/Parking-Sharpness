import Parking.Support.BoxTranslation
import Parking.Support.MatchedUniform

noncomputable section
namespace Parking
open LatticeProb
open scoped Classical
variable {d : ℕ}

theorem mem_box_zero_of_graphNorm_le {z : Site d} {R : ℕ} (hz : graphNorm z ≤ R) :
    z ∈ boxFinset (0 : Site d) R := by
  apply mem_boxFinset_iff.mpr
  intro i
  have hi : (z i).natAbs ≤ graphNorm z := by
    apply Finset.single_le_sum (f := fun j : Fin d => (z j).natAbs)
    · intro _ _; omega
    · exact Finset.mem_univ i
  have hc := (Int.ofNat_le).mpr (hi.trans hz)
  simpa using hc

/-- A finite sum split into a fixed inner region, a growing middle region and a far region. -/
theorem sum_three_shell_le (S : Finset (Site d)) (f : Site d → ℝ) (L M : ℕ)
    (B₀ B₁ B₂ : ℝ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₀ : ∀ z ∈ S, graphNorm z < L → f z ≤ B₀)
    (h₁ : ∀ z ∈ S, L ≤ graphNorm z → graphNorm z < M → f z ≤ B₁)
    (h₂ : ∀ z ∈ S, L ≤ graphNorm z → M ≤ graphNorm z → f z ≤ B₂) :
    (∑ z ∈ S, f z) ≤ ((2 * L + 1 : ℕ) : ℝ) ^ d * B₀ +
      ((2 * M + 1 : ℕ) : ℝ) ^ d * B₁ + (S.card : ℝ) * B₂ := by
  have hp : ∀ z ∈ S, f z ≤ (if graphNorm z < L then B₀ else 0) +
      (if graphNorm z < M then B₁ else 0) + B₂ := by
    intro z hz
    by_cases hzL : graphNorm z < L
    · have h := h₀ z hz hzL
      simp only [hzL, if_true]
      split_ifs <;> linarith
    · by_cases hzM : graphNorm z < M
      · have h := h₁ z hz (by omega) hzM
        simp only [hzL, hzM, if_false, if_true, zero_add]
        linarith
      · have h := h₂ z hz (by omega) (by omega)
        simpa only [hzL, hzM, if_false, zero_add] using h
  have hcount (K : ℕ) : ((S.filter fun z => graphNorm z < K).card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) ^ d := by
    have hs : (S.filter fun z => graphNorm z < K) ⊆ boxFinset (0 : Site d) K := by
      intro z hz
      exact mem_box_zero_of_graphNorm_le (Nat.le_of_lt (Finset.mem_filter.mp hz).2)
    have h := Finset.card_le_card hs
    rw [card_boxFinset] at h
    exact_mod_cast h
  have he (K : ℕ) (B : ℝ) : (∑ z ∈ S, if graphNorm z < K then B else 0) =
      ((S.filter fun z => graphNorm z < K).card : ℝ) * B := by
    rw [← Finset.sum_filter]
    simp
  calc (∑ z ∈ S, f z)
    ≤ ∑ z ∈ S, ((if graphNorm z < L then B₀ else 0) + (if graphNorm z < M then B₁ else 0) + B₂) := Finset.sum_le_sum hp
    _ = ((S.filter fun z => graphNorm z < L).card : ℝ) * B₀ +
        ((S.filter fun z => graphNorm z < M).card : ℝ) * B₁ + (S.card : ℝ) * B₂ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, he, he]
      simp
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_right (hcount L) hB₀)
      (mul_le_mul_of_nonneg_right (hcount M) hB₁)) le_rfl

end Parking
