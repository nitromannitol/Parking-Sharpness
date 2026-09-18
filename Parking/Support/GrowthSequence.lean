/-
Decreasing sequences and their partial sums: the power and logarithmic
comparisons used in the density estimates of the growth corollary.
-/
import Parking.Support.UpperTarget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace Parking
open Filter

/-- The last term of a decreasing sequence is bounded by its average. -/
theorem antitone_mul_le_sum (f : ℕ → ℝ) (hf : Antitone f) (n : ℕ) :
    ((n : ℝ) + 1) * f n ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  calc ((n : ℝ) + 1) * f n = ∑ _i ∈ Finset.range (n + 1), f n := by simp
    _ ≤ ∑ i ∈ Finset.range (n + 1), f i := by
      exact Finset.sum_le_sum fun i hi => hf (by simpa using Finset.mem_range.mp hi)

/-- A power bound for partial sums gives the corresponding pointwise bound
for any nonnegative decreasing sequence. -/
theorem antitone_power_bounds (f : ℕ → ℝ) (hf : Antitone f)
    (hf0 : ∀ n, 0 ≤ f n) {β c C : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ n : ℕ, 2 ≤ n → c * (n : ℝ) ^ β ≤ ∑ i ∈ Finset.range n, f i ∧
      (∑ i ∈ Finset.range n, f i) ≤ C * (n : ℝ) ^ β) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ t : ℕ,
      a * ((t : ℝ) + 1) ^ (β - 1) ≤ f t ∧
      f t ≤ b * ((t : ℝ) + 1) ^ (β - 1) := by
  have hlim : Tendsto (fun m : ℕ => (m : ℝ) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  obtain ⟨m, hm2, hm⟩ :=
    ((eventually_ge_atTop 2).and (hlim.eventually (eventually_ge_atTop (2 * C / c)))).exists
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmβ : 2 * C ≤ c * (m : ℝ) ^ β := by
    have := (div_le_iff₀ hc).mp hm
    nlinarith
  refine ⟨C / m * 2 ^ (β - 1), max C (f 0 + 1), by positivity,
    lt_of_lt_of_le hC (le_max_left _ _), fun t => ⟨?_, ?_⟩⟩
  · let n := t + 2
    have hn2 : 2 ≤ n := by dsimp [n]; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hmn : n ≤ m * n := by nlinarith
    have hmn2 : 2 ≤ m * n := le_trans hn2 hmn
    have hblock : (∑ i ∈ Finset.range (m * n), f i) -
        (∑ i ∈ Finset.range n, f i) ≤ (m : ℝ) * n * f n := by
      have heq : m * n = n + (m * n - n) := by omega
      rw [heq, Finset.sum_range_add, add_sub_cancel_left]
      calc (∑ i ∈ Finset.range (m * n - n), f (n + i))
          ≤ ∑ _i ∈ Finset.range (m * n - n), f n :=
            Finset.sum_le_sum fun i _ => hf (Nat.le_add_right n i)
        _ = ((m * n - n : ℕ) : ℝ) * f n := by simp
        _ ≤ (m : ℝ) * n * f n := by
          apply mul_le_mul_of_nonneg_right _ (hf0 n)
          exact_mod_cast (Nat.sub_le (m * n) n)
    have hscale : (m * n : ℕ) ^ β = (m : ℝ) ^ β * (n : ℝ) ^ β := by
      push_cast
      exact Real.mul_rpow hm0.le hn0.le
    have hlo := (hb (m * n) hmn2).1
    have hup := (hb n hn2).2
    rw [hscale] at hlo
    have hnβ : 0 ≤ (n : ℝ) ^ β := Real.rpow_nonneg hn0.le _
    have hnf : C * (n : ℝ) ^ β ≤ (m : ℝ) * n * f n := by
      nlinarith [mul_le_mul_of_nonneg_right hmβ hnβ]
    have hpoint : C / m * (n : ℝ) ^ (β - 1) ≤ f n := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
      apply (mul_le_mul_iff_right₀ (mul_pos hm0 hn0)).mp
      calc ((m : ℝ) * n) * (C / m * ((n : ℝ) ^ β / n))
          = C * (n : ℝ) ^ β := by field_simp
        _ ≤ ((m : ℝ) * n) * f n := hnf
    have hratio : 2 ^ (β - 1) * ((t : ℝ) + 1) ^ (β - 1) ≤
        (n : ℝ) ^ (β - 1) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
      apply Real.rpow_le_rpow_of_nonpos hn0
      · dsimp [n]; push_cast; linarith
      · linarith
    calc C / m * 2 ^ (β - 1) * ((t : ℝ) + 1) ^ (β - 1)
        ≤ C / m * (n : ℝ) ^ (β - 1) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ C / m)
      _ ≤ f n := hpoint
      _ ≤ f t := hf (by dsimp [n]; omega)
  · by_cases ht : t = 0
    · subst t
      simpa only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] using
        (le_trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
          (le_max_right C (f 0 + 1)))
    · have ht1 : 1 ≤ t := by omega
      have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have hmean := antitone_mul_le_sum f hf t
      have hup := (hb (t + 1) (by omega)).2
      rw [Nat.cast_add, Nat.cast_one] at hup
      have hfC : f t ≤ C * ((t : ℝ) + 1) ^ (β - 1) := by
        rw [Real.rpow_sub ht0, Real.rpow_one, ← mul_div_assoc]
        exact (le_div_iff₀ ht0).mpr (by nlinarith)
      exact hfC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg ht0.le _))

/-- An eventual reciprocal lower bound extends to all times by monotonicity. -/
theorem antitone_reciprocal_lower (f : ℕ → ℝ) (hf : Antitone f)
    (hf0 : ∀ n, 0 ≤ f n) {c : ℝ} (hc : 0 < c)
    (he : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) * f n) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℕ, a / ((t : ℝ) + 1) ≤ f t := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let M := max N 1
  have hNM : N ≤ M := le_max_left _ _
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1))
  have hMf : 0 < f M := (mul_pos_iff_of_pos_left hM0).mp (hc.trans_le (hN M hNM))
  refine ⟨min c (f M), lt_min hc hMf, fun t => ?_⟩
  have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  rw [div_le_iff₀ ht0]
  by_cases hMt : M ≤ t
  · have hct := hN t (hNM.trans hMt)
    have ha := min_le_left c (f M)
    nlinarith [hf0 t]
  · have hft := hf (show t ≤ M by omega)
    have ha := min_le_right c (f M)
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    nlinarith [mul_nonneg ht (hf0 t)]

/-- Logarithmic growth of partial sums bounds the density by log(t+2)/(t+1). -/
theorem antitone_log_upper (f : ℕ → ℝ) (hf : Antitone f)
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ n : ℕ, 2 ≤ n → (∑ i ∈ Finset.range n, f i) ≤ C * Real.log n) :
    ∃ b : ℝ, 0 < b ∧ ∀ t : ℕ,
      f t ≤ b * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1) := by
  refine ⟨max C ((f 0 + 1) / Real.log 2),
    lt_of_lt_of_le hC (le_max_left _ _), fun t => ?_⟩
  have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  rw [le_div_iff₀ ht0]
  by_cases ht : t = 0
  · subst t
    simp only [Nat.cast_zero, zero_add, mul_one]
    have ha := (div_le_iff₀ log_two_pos).mp (le_max_right C ((f 0 + 1) / Real.log 2))
    linarith
  · have hs := antitone_mul_le_sum f hf t
    have hb' := hb (t + 1) (by omega)
    rw [Nat.cast_add, Nat.cast_one] at hb'
    have hlog : Real.log ((t : ℝ) + 1) ≤ Real.log ((t : ℝ) + 2) :=
      Real.log_le_log ht0 (by linarith)
    have hlog0 : 0 ≤ Real.log ((t : ℝ) + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) t; linarith)
    have hC' := mul_le_mul_of_nonneg_right
      (le_max_left C ((f 0 + 1) / Real.log 2)) hlog0
    nlinarith
end Parking
