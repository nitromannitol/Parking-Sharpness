/-
The three explicit discrepancy rates and their power saving over the mean.
-/
import Parking.Support.UpperTarget

noncomputable section
namespace Parking

/-- The dimension-dependent rate in the low-dimensional odometer discrepancy. -/
def discrepancyRate (d n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((5 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)
  else if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4)
  else (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)

theorem discrepancyRate_pos (d : ℕ) {n : ℕ} (hn : 1 ≤ n) : 0 < discrepancyRate d n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  unfold discrepancyRate
  split_ifs <;> positivity

theorem one_le_log_succ {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.log ((n : ℝ) + 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_quarter_le_eighth {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤
      4 ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 8) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 1) := (zero_le_one.trans (one_le_log_succ hn))
  have h1 := log_succ_le_two_mul_log hn
  have h2 := log_le_two_rpow_half n
  have hb : Real.log ((n : ℝ) + 1) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 2) := by linarith
  have h := Real.rpow_le_rpow hL0 hb (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le] at h
  norm_num at h
  exact h

theorem eighth_log_le_discrepancyRate (d : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤
      discrepancyRate d n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL1 := one_le_log_succ hn
  unfold discrepancyRate
  split_ifs
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (Real.rpow_nonneg (by linarith) _)
  · exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
      (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  · exact le_rfl

theorem log_le_discrepancyRate (d : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 4 ^ ((1 : ℝ) / 4) * discrepancyRate d n := by
  have hL0 : 0 < Real.log ((n : ℝ) + 1) := zero_lt_one.trans_le (one_le_log_succ hn)
  have heq : Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) *
      Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) = Real.log ((n : ℝ) + 1) := by
    rw [← Real.rpow_add hL0]; norm_num
  calc Real.log ((n : ℝ) + 1)
      = Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) := heq.symm
    _ ≤ (4 ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 8)) *
        Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right (log_quarter_le_eighth hn) (Real.rpow_nonneg hL0.le _)
    _ ≤ 4 ^ ((1 : ℝ) / 4) * discrepancyRate d n := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (eighth_log_le_discrepancyRate d hn) (by positivity)

/-- The three square-root rates in dimensions one, two and three. -/
theorem sqrt_kappa_log_le_discrepancyRate {d n : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (hn : 2 ≤ n) :
    Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
      Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤ Real.sqrt 2 * discrepancyRate d n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < Real.log ((n : ℝ) + 1) := zero_lt_one.trans_le (one_le_log_succ hn)
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  interval_cases d
  · have heq : Real.sqrt (kappa 1 n * (n : ℝ) ^ ((4 - ((1 : ℕ) : ℝ)) / 4)) *
        Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) = discrepancyRate 1 n := by
      norm_num [kappa, discrepancyRate]
      rw [← Real.rpow_add hn0, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
      norm_num
    rw [heq]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs2
      (discrepancyRate_pos (n := n) 1 (by omega)).le
  · have hk : kappa 2 n ≤ 2 * Real.log ((n : ℝ) + 1) := by
      norm_num [kappa]
      have h1 := log_add_two_le_two_mul_log hn
      have h2 := Real.log_le_log hn0 (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
      linarith
    have hq : Real.sqrt ((n : ℝ) ^ ((1 : ℝ) / 2)) = (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; norm_num
    have hLq : Real.sqrt (Real.log ((n : ℝ) + 1)) =
        Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hLp : Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) *
        Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) =
          Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4) := by
      rw [← Real.rpow_add hL0]; norm_num
    norm_num
    calc Real.sqrt (kappa 2 n * (n : ℝ) ^ ((1 : ℝ) / 2)) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)
        ≤ Real.sqrt ((2 * Real.log ((n : ℝ) + 1)) * (n : ℝ) ^ ((1 : ℝ) / 2)) *
            Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
            (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hn0.le _))) (Real.rpow_nonneg hL0.le _)
      _ = Real.sqrt 2 * discrepancyRate 2 n := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.log ((n : ℝ) + 1)),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hq, hLq]
        norm_num [discrepancyRate]
        calc Real.sqrt 2 * Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) *
            Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) =
            Real.sqrt 2 * (n : ℝ) ^ ((1 : ℝ) / 4) * (Real.log ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) *
              Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)) := by ring
          _ = _ := by rw [hLp]; ring
  · have heq : Real.sqrt (kappa 3 n * (n : ℝ) ^ ((4 - ((3 : ℕ) : ℝ)) / 4)) *
        Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) = discrepancyRate 3 n := by
      norm_num [kappa, discrepancyRate]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
      norm_num
    rw [heq]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs2
      (discrepancyRate_pos (n := n) 3 (by omega)).le
end Parking

namespace Parking

/-- Relative to the mean sandpile scale, every discrepancy rate saves a power. -/
theorem discrepancyRate_le_power {d n : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (hn : 2 ≤ n) :
    discrepancyRate d n ≤ (n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) *
      Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL1 := one_le_log_succ hn
  interval_cases d
  · norm_num [discrepancyRate]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) (Real.rpow_nonneg (by linarith) _)
  · norm_num [discrepancyRate]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (Real.rpow_nonneg (by linarith) _)
  · norm_num [discrepancyRate]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) (Real.rpow_nonneg (by linarith) _)
end Parking
