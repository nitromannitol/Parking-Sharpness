/- Averaged spatial shift energy bounds the difference between delayed binomial layers. -/
import Parking.Support.BinomialConvolution

noncomputable section
namespace Parking
open Finset

theorem summable_binom_difference_sq (n m : ℕ) (a b : ℤ) :
    Summable fun j : ℤ => (binomLaw n (j - a) - binomLaw m (j - b)) ^ 2 := by
  refine summable_of_ne_finset_zero (s := Icc (min a b) (max ((n : ℤ) + a) ((m : ℤ) + b))) ?_
  intro j hj
  simp only [mem_Icc, not_and_or, not_le, lt_min_iff, max_lt_iff] at hj
  rcases hj with hj | hj
  · rw [binomLaw_of_neg n (by omega), binomLaw_of_neg m (by omega)]
    norm_num
  · rw [binomLaw_of_gt n (by omega), binomLaw_of_gt m (by omega)]
    norm_num

theorem tsum_binom_shift_difference (n : ℕ) (a b : ℤ) :
    (∑' j : ℤ, (binomLaw n (j - a) - binomLaw n (j - b)) ^ 2) =
      ∑' j : ℤ, (binomLaw n (j - (a - b)) - binomLaw n j) ^ 2 := by
  have he := (Equiv.addRight b).tsum_eq
    (fun j : ℤ => (binomLaw n (j - a) - binomLaw n (j - b)) ^ 2)
  simp only [Equiv.coe_addRight, add_sub_cancel_right,
    show ∀ j : ℤ, j + b - a = j - (a - b) from fun j => by ring] at he
  exact he.symm

theorem sum_binom_shift_difference_le (N : ℕ) (a b : ℤ) :
    (∑ n ∈ range N, ∑' j : ℤ, (binomLaw n (j - a) - binomLaw n (j - b)) ^ 2) ≤
      4 * |((a - b : ℤ) : ℝ)| := by
  simp only [tsum_binom_shift_difference]
  rw [← (shift_energy (a - b)).2.2]
  exact (shift_energy (a - b)).2.1.sum_le_tsum (range N)
    (fun n _ => tsum_nonneg fun j => sq_nonneg _)

theorem tsum_binom_convolution_difference_le (n h : ℕ) (D : ℤ) :
    (∑' j : ℤ, (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2) ≤
      ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k *
        ∑' j : ℤ, (binomLaw n (j - k) - binomLaw n (j - D)) ^ 2 := by
  have hs : Summable fun j : ℤ => (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2 := by
    simpa only [sub_zero] using summable_binom_difference_sq (n + h) n 0 D
  have hr : ∀ k : ℤ, Summable fun j : ℤ =>
      binomLaw h k * (binomLaw n (j - k) - binomLaw n (j - D)) ^ 2 :=
    fun k => (summable_binom_difference_sq n n k D).mul_left _
  have hb := hs.tsum_le_tsum (fun j => binomLaw_convolution_difference_sq n h j D)
    (summable_sum (s := Icc (0 : ℤ) (h : ℤ)) (fun k _ => hr k))
  rw [Summable.tsum_finsetSum (fun k _ => hr k)] at hb
  simpa only [tsum_mul_left] using hb

/-- Time convolution costs at most the averaged shift energy, uniformly in
the number of retained layers. -/
theorem sum_binom_delay_difference_le (N h : ℕ) (D : ℤ) :
    (∑ n ∈ range N, ∑' j : ℤ, (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2) ≤
      4 * ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k * |((k - D : ℤ) : ℝ)| := by
  calc _ ≤ ∑ n ∈ range N, ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k *
        ∑' j : ℤ, (binomLaw n (j - k) - binomLaw n (j - D)) ^ 2 :=
      sum_le_sum fun n _ => tsum_binom_convolution_difference_le n h D
    _ = ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k *
        ∑ n ∈ range N, ∑' j : ℤ, (binomLaw n (j - k) - binomLaw n (j - D)) ^ 2 := by
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k * (4 * |((k - D : ℤ) : ℝ)|) :=
      sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (sum_binom_shift_difference_le N k D)
        (binomLaw_nonneg h k)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro k _; ring

end Parking
