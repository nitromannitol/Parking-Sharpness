/-
Extending asymptotic lower bounds across a finite positive prefix.
-/
import Mathlib

noncomputable section
namespace Parking
open Filter

/-- An eventual multiplicative lower bound extends over a finite positive prefix after shrinking its constant. -/
theorem extend_positive_lower_bound (f g : ℕ → ℝ) (m : ℕ)
    (hf : ∀ n, m ≤ n → 0 < f n) (hg : ∀ n, m ≤ n → 0 < g n)
    {c : ℝ} (hc : 0 < c) (he : ∀ᶠ n in atTop, c * g n ≤ f n) :
    ∃ a : ℝ, 0 < a ∧ a ≤ c ∧ ∀ n, m ≤ n → a * g n ≤ f n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hfin : ∀ K : ℕ, ∃ a : ℝ, 0 < a ∧ a ≤ c ∧
      ∀ n, m ≤ n → n < K → a * g n ≤ f n := by
    intro K
    induction K with
    | zero => exact ⟨c, hc, le_rfl, fun n _ hn => (Nat.not_lt_zero n hn).elim⟩
    | succ K ih =>
        obtain ⟨a, ha, hac, hfa⟩ := ih
        by_cases hK : m ≤ K
        · refine ⟨min a (f K / g K), lt_min ha (div_pos (hf K hK) (hg K hK)),
            (min_le_left _ _).trans hac, fun n hn hnK => ?_⟩
          by_cases hnK' : n = K
          · subst n
            exact (le_div_iff₀ (hg K hK)).mp (min_le_right _ _)
          · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hg n hn).le).trans
              (hfa n hn (by omega))
        · exact ⟨a, ha, hac, fun n hn hnK => hfa n hn (by omega)⟩
  obtain ⟨a, ha, hac, hfa⟩ := hfin N
  refine ⟨a, ha, hac, fun n hn => ?_⟩
  by_cases hnN : n < N
  · exact hfa n hn hnN
  · exact (mul_le_mul_of_nonneg_right hac (hg n hn).le).trans (hN n (by omega))
end Parking
