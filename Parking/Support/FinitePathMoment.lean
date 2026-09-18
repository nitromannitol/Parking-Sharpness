/- A finite-path maximal inequality from moment bounds on increments. -/
import Parking.Support.DyadicMoment
import Mathlib.Data.Nat.Log

noncomputable section
namespace Parking
open MeasureTheory Finset

def finitePathMax (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' (by simp) (fun j => |f j|)

theorem abs_le_finitePathMax (f : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    |f j| ≤ finitePathMax f n :=
  le_sup' (fun j => |f j|) (mem_range.mpr (by omega))

theorem finitePathMax_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ finitePathMax f n :=
  (abs_nonneg (f 0)).trans (abs_le_finitePathMax f n 0 (Nat.zero_le _))

theorem finitePathMax_le (f : ℕ → ℝ) (n : ℕ) {b : ℝ}
    (h : ∀ j : ℕ, j ≤ n → |f j| ≤ b) : finitePathMax f n ≤ b :=
  sup'_le _ _ (fun j hj => h j (by have := mem_range.mp hj; omega))

theorem measurable_finitePathMax {Ω : Type} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (F i)) (n : ℕ) :
    Measurable fun ω => finitePathMax (fun i => F i ω) n := by
  exact Finset.measurable_range_sup'' (fun j _ => (hm j).abs)

variable {Ω : Type} [MeasurableSpace Ω]

/-- A constant independent of the number of time points controls the maximum
whenever the time increment exponent is strictly greater than `1/r`. -/
theorem exists_finitePathMax_moment (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r)
    (a : ℝ) (ha : 1 / r < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (F : ℕ → Ω → ℝ),
      (∀ i, Measurable (F i)) → (∀ ω, F 0 ω = 0) → ∀ C : ℝ, 0 ≤ C →
      (∀ j k : ℕ, j ≤ k → k ≤ n →
        Integrable (fun ω => |F k ω - F j ω| ^ r) μ ∧
        rNorm μ r (fun ω => F k ω - F j ω) ≤ C * ((k - j : ℕ) : ℝ) ^ a) →
      Integrable (fun ω => |finitePathMax (fun i => F i ω) n| ^ r) μ ∧
        rNorm μ r (fun ω => finitePathMax (fun i => F i ω) n) ≤ K * C * (n : ℝ) ^ a := by
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := lt_trans (by positivity : (0 : ℝ) < 1 / r) ha
  let A : ℝ := 2 ^ a
  let b : ℝ := 2 ^ (1 / r)
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : b < A := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ha
  let K := (A / (A - b)) * A
  have hK : 0 < K := mul_pos (div_pos hA (sub_pos.mpr hlt)) hA
  refine ⟨K, hK, fun n hn F hm hz C hC hinc => ?_⟩
  let L := Nat.log 2 n + 1
  have hn0 : n ≠ 0 := by omega
  have hnL : n ≤ 2 ^ L := (Nat.lt_pow_of_log_lt (by norm_num) (Nat.lt_succ_self _)).le
  have hLn : 2 ^ L ≤ 2 * n := by
    dsimp only [L]
    rw [pow_succ]
    have h := Nat.pow_log_le_self 2 hn0
    omega
  let G : ℕ → Ω → ℝ := fun i => F (min i n)
  have hGm : ∀ i, Measurable (G i) := fun i => hm _
  have hGinc : ∀ j k : ℕ, j ≤ k → k ≤ 2 ^ L →
      Integrable (fun ω => |G k ω - G j ω| ^ r) μ ∧
      rNorm μ r (fun ω => G k ω - G j ω) ≤ C * ((k - j : ℕ) : ℝ) ^ a := by
    intro j k hjk _
    obtain ⟨hi, hbnd⟩ := hinc (min j n) (min k n) (by omega) (by omega)
    refine ⟨hi, hbnd.trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ ha0.le
    exact_mod_cast (show min k n - min j n ≤ k - j by omega)
  obtain ⟨hei, heb⟩ := dyadicEnvelope_moment μ hr a L G hGm hC hGinc
  let E : Ω → ℝ := fun ω => dyadicEnvelope r (fun i => G i ω) L
  let M : Ω → ℝ := fun ω => finitePathMax (fun i => F i ω) n
  have hM0 (ω : Ω) : 0 ≤ M ω := finitePathMax_nonneg _ _
  have hE0 (ω : Ω) : 0 ≤ E ω := dyadicEnvelope_nonneg _ _ _
  have hME (ω : Ω) : M ω ≤ E ω := by
    apply finitePathMax_le
    intro j hj
    have h := abs_sub_le_dyadicEnvelope hr0 (fun i => G i ω) L j (hj.trans hnL)
    have h0 : G 0 ω = 0 := by simp only [G, Nat.zero_min, hz]
    rw [h0, sub_zero] at h
    simpa only [G, min_eq_left hj] using h
  have hMi : Integrable (fun ω => |M ω| ^ r) μ := by
    refine hei.mono' (((measurable_finitePathMax F hm n).abs.pow_const r).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r),
      abs_of_nonneg (hM0 ω), abs_of_nonneg (hE0 ω)]
    exact Real.rpow_le_rpow (hM0 ω) (hME ω) hr0.le
  have hmono := rNorm_mono μ hr0 (Filter.Eventually.of_forall fun ω => by
    rw [abs_of_nonneg (hM0 ω), abs_of_nonneg (hE0 ω)]
    exact hME ω) hei
  refine ⟨hMi, hmono.trans (heb.trans ?_)⟩
  have hf := mul_le_mul_of_nonneg_left (dyadicFactor_le hb.le hlt L) hC
  have hp : A ^ L ≤ A * (n : ℝ) ^ a := by
    change (2 ^ a : ℝ) ^ L ≤ _
    rw [Real.rpow_pow_comm (by norm_num)]
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ L)
      (show (2 : ℝ) ^ L ≤ 2 * (n : ℝ) by exact_mod_cast hLn) ha0.le
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)] at h
  have hmulp := mul_le_mul_of_nonneg_left hp (mul_nonneg hC (div_nonneg hA.le (sub_pos.mpr hlt).le))
  exact hf.trans (by simpa only [K, mul_assoc, mul_comm, mul_left_comm] using hmulp)

end Parking
