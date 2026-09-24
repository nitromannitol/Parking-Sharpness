/-
The Green rates of `eq:green-norms` against the scale `φ_d` of Section 9.

Step 1 of `lem:mean-horizon` adds the mean of the odometer, which `thm:BP`
bounds by `C φ_d(m)`, to the concentration term `√r ‖g_m‖₂ + r max_x g_m(x)`,
and reads the sum as `C_r φ_d(m)`.  That reading is the content of this file:
in dimensions one to three the rate of `‖g_m‖₂` IS the scale `φ_d` up to the
shift of the argument, and the rate of `max_x g_m(x)` is a smaller power; in
dimension four `√(log m) ≤ 2 log m`; and from dimension five both rates are the
constant one, which is below `log(m+2)`.  Everything is read at `m ≥ 2`, the
range in which `eq:green-norms` is stated.
-/
import Parking.Support.PhiSum
import Parking.External.GreenNorms

noncomputable section

namespace Parking

open Parking.External

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h1
  linarith

theorem sqrt_le_two_mul {t : ℝ} (ht : 1/4 ≤ t) : Real.sqrt t ≤ 2 * t := by
  have ht0 : (0:ℝ) ≤ t := by linarith
  have h : t ≤ (2 * t) ^ 2 := by nlinarith
  calc Real.sqrt t ≤ Real.sqrt ((2 * t) ^ 2) := Real.sqrt_le_sqrt h
    _ = 2 * t := Real.sqrt_sq (by linarith)

theorem one_le_log_add_two {m : ℕ} (hm : 2 ≤ m) : 1 ≤ 2 * Real.log ((m : ℝ) + 2) := by
  have hm4 : (4:ℝ) ≤ (m : ℝ) + 2 := by
    have : (2:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have h2 : Real.log 4 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) hm4
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

theorem log_ge_quarter {m : ℕ} (hm : 2 ≤ m) : 1/4 ≤ Real.log (m : ℝ) := by
  have hm2 : (2:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm2
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

/-- **Both Green rates are below the scale `φ_d`.**  The rate of `‖g_n‖₂` in
`eq:green-norms` is exactly the scale `φ_d` in dimensions one to three, and the rate of
`max_x g_n(x)` is smaller; in dimension four the square root of a logarithm is below a
logarithm, and from dimension five both rates are constant. -/
theorem exists_green_phi (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      greenL2Rate d m ≤ C * phi d m ∧ greenMaxRate d m ≤ C * phi d m := by
  refine ⟨2, by norm_num, fun m hm => ?_⟩
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmp1 : (1:ℝ) ≤ (m:ℝ) + 1 := by linarith
  have hbase : ∀ e : ℝ, 0 ≤ e → (m:ℝ) ^ e ≤ ((m:ℝ) + 1) ^ e :=
    fun e he => Real.rpow_le_rpow hm0 (by linarith) he
  have hexp : ∀ e f : ℝ, e ≤ f → ((m:ℝ) + 1) ^ e ≤ ((m:ℝ) + 1) ^ f :=
    fun e f hef => Real.rpow_le_rpow_of_exponent_le hmp1 hef
  have hone : ∀ e : ℝ, 0 ≤ e → (1:ℝ) ≤ ((m:ℝ) + 1) ^ e :=
    fun e he => Real.one_le_rpow hmp1 he
  by_cases h1 : d = 1
  · subst h1
    constructor
    · simp only [greenL2Rate, phi, if_pos (by norm_num : (1:ℕ) ≤ 3)]
      norm_num
      nlinarith [hbase ((3:ℝ)/4) (by norm_num), hone ((3:ℝ)/4) (by norm_num)]
    · simp only [greenMaxRate, phi, if_pos (by norm_num : (1:ℕ) ≤ 3)]
      norm_num
      nlinarith [hbase ((1:ℝ)/2) (by norm_num), hexp ((1:ℝ)/2) ((3:ℝ)/4) (by norm_num),
        hone ((3:ℝ)/4) (by norm_num)]
  by_cases h2 : d = 2
  · subst h2
    constructor
    · simp only [greenL2Rate, phi, if_neg (by norm_num : ¬(2:ℕ) = 1),
        if_pos (by norm_num : (2:ℕ) ≤ 3)]
      norm_num
      nlinarith [hbase ((1:ℝ)/2) (by norm_num), hone ((1:ℝ)/2) (by norm_num)]
    · simp only [greenMaxRate, phi, if_neg (by norm_num : ¬(2:ℕ) = 1),
        if_pos (by norm_num : (2:ℕ) ≤ 3)]
      norm_num
      have hlog := log_le_two_sqrt (show (0:ℝ) < (m:ℝ) by linarith)
      have hsq : Real.sqrt (m:ℝ) = (m:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
      rw [hsq] at hlog
      nlinarith [hbase ((1:ℝ)/2) (by norm_num), hlog]
  by_cases h3 : d = 3
  · subst h3
    constructor
    · simp only [greenL2Rate, phi, if_neg (by norm_num : ¬(3:ℕ) = 1),
        if_neg (by norm_num : ¬(3:ℕ) = 2), if_pos (by norm_num : (3:ℕ) ≤ 3)]
      norm_num
      nlinarith [hbase ((1:ℝ)/4) (by norm_num), hone ((1:ℝ)/4) (by norm_num)]
    · simp only [greenMaxRate, phi, if_neg (by norm_num : ¬(3:ℕ) = 1),
        if_neg (by norm_num : ¬(3:ℕ) = 2), if_pos (by norm_num : (3:ℕ) ≤ 3)]
      norm_num
      nlinarith [hone ((1:ℝ)/4) (by norm_num)]
  · have hd4 : 4 ≤ d := by omega
    have hphi : phi d (m:ℝ) = Real.log ((m:ℝ) + 2) := by
      rw [phi, if_neg (by omega : ¬ d ≤ 3)]
    have hlogm : Real.log (m:ℝ) ≤ Real.log ((m:ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlog14 : 1/4 ≤ Real.log (m:ℝ) := log_ge_quarter hm
    have hone2 : 1 ≤ 2 * Real.log ((m:ℝ) + 2) := one_le_log_add_two hm
    have hmax : greenMaxRate d (m:ℕ) = 1 := by
      rw [greenMaxRate, if_neg (by omega : ¬ d = 1), if_neg (by omega : ¬ d = 2)]
    by_cases h4 : d = 4
    · subst h4
      refine ⟨?_, ?_⟩
      · rw [greenL2Rate, if_neg (by norm_num : ¬(4:ℕ) = 1), if_neg (by norm_num : ¬(4:ℕ) = 2),
          if_neg (by norm_num : ¬(4:ℕ) = 3), hphi]
        calc Real.sqrt (Real.log (m:ℝ)) ≤ 2 * Real.log (m:ℝ) := sqrt_le_two_mul hlog14
          _ ≤ 2 * Real.log ((m:ℝ) + 2) := by linarith
      · rw [hmax, hphi]; linarith
    · have hd5 : 5 ≤ d := by omega
      have hl2 : greenL2Rate d (m:ℕ) = 1 := by
        rw [greenL2Rate, if_neg (by omega : ¬ d = 1), if_neg (by omega : ¬ d = 2),
          if_neg (by omega : ¬ d = 3), if_neg (by omega : ¬ d = 4)]
      refine ⟨?_, ?_⟩
      · rw [hl2, hphi]; linarith
      · rw [hmax, hphi]; linarith

end Parking

end
