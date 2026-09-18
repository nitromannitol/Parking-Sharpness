/- Directed Green square norms in the logarithmic and summable dimensions. -/
import Parking.Support.OrientedLayerBounds
import Parking.Support.OrientedNormPositive
import Parking.Support.CriticalReduction

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

theorem orientedGreen_sq_split (n : ℕ) (hn : 1 ≤ n) :
    (∑' x : Site d, orientedGreen d n x ^ 2) =
      1 + ∑ l ∈ Ico 1 n, ∑' x : Site d, orientedLayer d l x ^ 2 := by
  rw [tsum_orientedGreen_sq]
  have hs : range n = insert 0 (Ico 1 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  rw [hs, sum_insert (by simp)]
  simp [orientedLayer]

theorem log_nat_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 1 + Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    (show (n : ℝ) + 1 ≤ 2 * n by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : (n : ℝ) ≠ 0)] at h
  linarith [Real.log_two_lt_d9]

theorem exists_orientedGreen_three_sq_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      c * Real.log ((n : ℝ) + 1) ≤ ∑' x : Site 3, orientedGreen 3 n x ^ 2 ∧
        (∑' x : Site 3, orientedGreen 3 n x ^ 2) ≤ C * Real.log ((n : ℝ) + 1) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_orientedLayer_sq_bounds (d := 3) (by norm_num)
  refine ⟨min 1 c, 2 + 3 * C, lt_min zero_lt_one hc, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlo : c * (∑ l ∈ Ico 1 n, (1 : ℝ) / l) ≤
      ∑ l ∈ Ico 1 n, ∑' x : Site 3, orientedLayer 3 l x ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro l hl
    have h := (hb l (mem_Ico.mp hl).1).1
    norm_num only [show (3 : ℕ) - 1 = 2 by omega, Real.sq_sqrt (Nat.cast_nonneg l)] at h
    simpa only [mul_one_div] using h
  have hhi : (∑ l ∈ Ico 1 n, ∑' x : Site 3, orientedLayer 3 l x ^ 2) ≤
      C * (∑ l ∈ Ico 1 n, (l : ℝ)⁻¹) := by
    rw [mul_sum]
    apply sum_le_sum
    intro l hl
    have h := (hb l (mem_Ico.mp hl).1).2
    norm_num only [show (3 : ℕ) - 1 = 2 by omega, Real.sq_sqrt (Nat.cast_nonneg l)] at h
    simpa only [div_eq_mul_inv] using h
  have hharlo := log_sub_log_le_sum_inv (T := 1) (by norm_num) n hn
  simp only [Nat.cast_one, Real.log_one, sub_zero] at hharlo
  have hharhi := sum_inv_le_one_add_log n
  have hmullo := mul_le_mul_of_nonneg_left hharlo hc.le
  have hmulhi := mul_le_mul_of_nonneg_left hharhi hC.le
  have hlgn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogone : 1 ≤ 2 * Real.log ((n : ℝ) + 1) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ (n : ℝ) + 1 by linarith)
    linarith [Real.log_two_gt_d9]
  rw [orientedGreen_sq_split n hn]
  constructor
  · have hmin1 := min_le_left (1 : ℝ) c
    have hminc := min_le_right (1 : ℝ) c
    have hmin0 : 0 ≤ min (1 : ℝ) c := (lt_min zero_lt_one hc).le
    have h1 := mul_le_mul_of_nonneg_left (log_nat_add_one_le n hn) hmin0
    have h2 := mul_le_mul_of_nonneg_right hminc hlog
    nlinarith
  · nlinarith

theorem exists_orientedGreen_high_sq_bound (hd : 4 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (∑' x : Site d, orientedGreen d n x ^ 2) ≤ C := by
  obtain ⟨c, C, _hc, hC, hb⟩ := exists_orientedLayer_sq_bounds (d := d) (by omega)
  refine ⟨1 + 3 * C, by positivity, fun n hn => ?_⟩
  have hsum : (∑ l ∈ Ico 1 n, ∑' x : Site d, orientedLayer d l x ^ 2) ≤
      C * ∑ l ∈ Ico 1 n, (l : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro l hl
    refine (hb l (mem_Ico.mp hl).1).2.trans ?_
    rw [div_eq_mul_inv, ← rpow_neg_half_eq]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (mem_Ico.mp hl).1)
    have hdR : (3 : ℝ) ≤ (d - 1 : ℕ) := by exact_mod_cast (show 3 ≤ d - 1 by omega)
    linarith
  rw [orientedGreen_sq_split n hn]
  have h := mul_le_mul_of_nonneg_left (sum_rpow_three_halves_le n) hC.le
  linarith

end Parking
