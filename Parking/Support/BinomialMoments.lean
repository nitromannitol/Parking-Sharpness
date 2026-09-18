/- Centered first and second moments of the fair binomial law. -/
import Parking.Support.BinomialConvolution

noncomputable section
namespace Parking
open Finset

theorem summable_binomLaw_weight (n : ℕ) (f : ℤ → ℝ) : Summable fun j => f j * binomLaw n j := by
  refine summable_of_ne_finset_zero (s := Icc (0 : ℤ) (n : ℤ)) fun j hj => ?_
  rw [binomLaw_zero_outside hj, mul_zero]

theorem tsum_binom_succ_weight (n : ℕ) (f : ℤ → ℝ) :
    (∑' j : ℤ, f j * binomLaw (n + 1) j) =
      ((∑' j : ℤ, f (j + 1) * binomLaw n j) + ∑' j : ℤ, f j * binomLaw n j) / 2 := by
  have hs : Summable fun j : ℤ => f j * binomLaw n (j - 1) := by
    have h := ((Equiv.addRight (-1 : ℤ)).summable_iff
      (f := fun j : ℤ => f (j + 1) * binomLaw n j)).mpr
      (summable_binomLaw_weight n (fun j => f (j + 1)))
    simpa only [Function.comp_def, Equiv.coe_addRight, show ∀ j : ℤ, j + -1 + 1 = j from fun j => by omega, sub_eq_add_neg] using h
  have he : ∀ j : ℤ, f j * binomLaw (n + 1) j =
      (f j * binomLaw n (j - 1) + f j * binomLaw n j) / 2 := by
    intro j
    rw [binomLaw_succ]
    ring
  have ht : (∑' j : ℤ, f j * binomLaw n (j - 1)) = ∑' j : ℤ, f (j + 1) * binomLaw n j := by
    have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun j : ℤ => f j * binomLaw n (j - 1))
    simpa only [Equiv.coe_addRight, add_sub_cancel_right] using h.symm
  rw [tsum_congr he, tsum_div_const, hs.tsum_add (summable_binomLaw_weight n f), ht]

theorem tsum_binom_first_moment (n : ℕ) : ∑' j : ℤ, (j : ℝ) * binomLaw n j = (n : ℝ) / 2 := by
  induction n with
  | zero => simp [binomLaw_zero]
  | succ n ih =>
    rw [tsum_binom_succ_weight]
    have he : ∀ j : ℤ, ((j + 1 : ℤ) : ℝ) * binomLaw n j =
        (j : ℝ) * binomLaw n j + binomLaw n j := by
      intro j
      push_cast
      ring
    have hs : Summable (binomLaw n) := by simpa using summable_binomLaw_weight n (fun _ => (1 : ℝ))
    rw [tsum_congr he, (summable_binomLaw_weight n (fun j => (j : ℝ))).tsum_add hs,
      ih, tsum_binomLaw]
    push_cast
    ring

theorem tsum_binom_second_moment (n : ℕ) :
    (∑' j : ℤ, (j : ℝ) ^ 2 * binomLaw n j) = ((n : ℝ) ^ 2 + n) / 4 := by
  induction n with
  | zero => simp [binomLaw_zero]
  | succ n ih =>
    rw [tsum_binom_succ_weight]
    have he : ∀ j : ℤ, ((j + 1 : ℤ) : ℝ) ^ 2 * binomLaw n j =
        (j : ℝ) ^ 2 * binomLaw n j + 2 * ((j : ℝ) * binomLaw n j) + binomLaw n j := by
      intro j
      push_cast
      ring
    have hs : Summable (binomLaw n) := by simpa using summable_binomLaw_weight n (fun _ => (1 : ℝ))
    have h1 := summable_binomLaw_weight n (fun j => (j : ℝ) ^ 2)
    have h2 := (summable_binomLaw_weight n (fun j => (j : ℝ))).mul_left 2
    rw [tsum_congr he, (h1.add h2).tsum_add hs, h1.tsum_add h2, tsum_mul_left,
      ih, tsum_binom_first_moment, tsum_binomLaw]
    push_cast
    ring

theorem sum_binom_variance (n : ℕ) :
    (∑ j ∈ Icc (0 : ℤ) (n : ℤ), binomLaw n j * ((j : ℝ) - (n : ℝ) / 2) ^ 2) = (n : ℝ) / 4 := by
  have he : ∀ j : ℤ, binomLaw n j * ((j : ℝ) - (n : ℝ) / 2) ^ 2 =
      (j : ℝ) ^ 2 * binomLaw n j - (n : ℝ) * ((j : ℝ) * binomLaw n j) +
        ((n : ℝ) ^ 2 / 4) * binomLaw n j := by
    intro j
    ring
  have ht : (∑' j : ℤ, binomLaw n j * ((j : ℝ) - (n : ℝ) / 2) ^ 2) =
      ∑ j ∈ Icc (0 : ℤ) (n : ℤ), binomLaw n j * ((j : ℝ) - (n : ℝ) / 2) ^ 2 :=
    tsum_eq_sum (fun j hj => by rw [binomLaw_zero_outside hj, zero_mul])
  rw [← ht, tsum_congr he]
  have h1 := summable_binomLaw_weight n (fun j => (j : ℝ) ^ 2)
  have h2 := (summable_binomLaw_weight n (fun j => (j : ℝ))).mul_left (n : ℝ)
  have h3 := summable_binomLaw_weight n (fun _ => (n : ℝ) ^ 2 / 4)
  rw [(h1.sub h2).tsum_add h3, h1.tsum_sub h2, tsum_mul_left,
    tsum_binom_second_moment, tsum_binom_first_moment, tsum_mul_left, tsum_binomLaw]
  ring

theorem sum_binom_abs_centered_le (n : ℕ) :
    (∑ j ∈ Icc (0 : ℤ) (n : ℤ), binomLaw n j * |(j : ℝ) - (n : ℝ) / 2|) ≤ Real.sqrt n / 2 := by
  have h := square_weighted_sum_le (Icc (0 : ℤ) (n : ℤ)) (binomLaw n)
    (fun j => |(j : ℝ) - (n : ℝ) / 2|) (fun j _ => binomLaw_nonneg n j) (sum_binomLaw n)
  simp only [sq_abs, sum_binom_variance] at h
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn : 0 ≤ ∑ j ∈ Icc (0 : ℤ) (n : ℤ), binomLaw n j * |(j : ℝ) - (n : ℝ) / 2| :=
    sum_nonneg fun j _ => mul_nonneg (binomLaw_nonneg n j) (abs_nonneg _)
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

theorem sum_binom_abs_shift_le (n : ℕ) (D : ℤ) :
    (∑ j ∈ Icc (0 : ℤ) (n : ℤ), binomLaw n j * |((j - D : ℤ) : ℝ)|) ≤
      Real.sqrt n / 2 + |(D : ℝ) - (n : ℝ) / 2| := by
  have h : ∀ j : ℤ, |((j - D : ℤ) : ℝ)| ≤
      |(j : ℝ) - (n : ℝ) / 2| + |(D : ℝ) - (n : ℝ) / 2| := by
    intro j
    rw [Int.cast_sub]
    have he : (j : ℝ) - D = ((j : ℝ) - (n : ℝ) / 2) - ((D : ℝ) - (n : ℝ) / 2) := by ring
    rw [he]
    exact abs_sub' _ _
  have hs := sum_le_sum (s := Icc (0 : ℤ) (n : ℤ))
    (fun j _ => mul_le_mul_of_nonneg_left (h j) (binomLaw_nonneg n j))
  simp only [mul_add, sum_add_distrib, ← sum_mul, sum_binomLaw, one_mul] at hs
  exact hs.trans (add_le_add (sum_binom_abs_centered_le n) le_rfl)

end Parking
