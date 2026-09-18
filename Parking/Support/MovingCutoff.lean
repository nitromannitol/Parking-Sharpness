import Mathlib

noncomputable section
namespace Parking
open Filter Topology

/-- A power-scale intermediate cutoff makes both the interaction exponent and the middle shell small. -/
theorem eventually_exists_middle_cutoff (d : ℕ) (hd : 5 ≤ d) (C : ℝ) (hC : 0 < C)
    (h : ℕ → ℝ) (hh : ∀ t, 0 < h t) (hh1 : ∀ t, h t ≤ 1)
    (hlim : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ t in atTop, ∃ M : ℕ,
      C * Real.log (1 / h t) * (1 + (M : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 ∧
      ((2 * M + 1 : ℕ) : ℝ) ^ d * (C * (h t) ^ (7 / 4 : ℝ)) ≤ h t / 8 := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  let a : ℝ := -1 / (4 * (d : ℝ))
  let r : ℝ := a * (4 - (d : ℝ))
  have ha : a < 0 := by
    dsimp only [a]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hr : 0 < r := mul_pos_of_neg_of_neg ha (by linarith)
  have hlim' : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hh⟩
  have hfar : Tendsto (fun t => C * Real.log (1 / h t) * (h t) ^ r) atTop (𝓝 0) := by
    have ht := ((tendsto_log_mul_rpow_nhdsGT_zero hr).comp hlim').neg.const_mul C
    simpa only [Function.comp_def, one_div, Real.log_inv, neg_mul, mul_assoc, neg_zero, mul_zero] using ht
  have hsmall : Tendsto (fun t => C * (3 : ℝ) ^ d * (h t) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have ht := ((Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 2 : ℝ))).tendsto 0).comp hlim
    have ht' := ht.const_mul (C * (3 : ℝ) ^ d)
    simpa only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero, Function.comp_def] using ht'
  filter_upwards [hfar.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmall.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with t hF hS
  let S : ℝ := (h t) ^ a
  let M : ℕ := Nat.floor S
  have hS0 : 0 < S := Real.rpow_pos_of_pos (hh t) _
  have hS1 : 1 ≤ S := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hh t) (hh1 t) ha.le
  have hM : (M : ℝ) ≤ S := Nat.floor_le hS0.le
  have hMS : S ≤ 1 + (M : ℝ) := by simpa only [add_comm] using (Nat.lt_floor_add_one S).le
  refine ⟨M, ?_, ?_⟩
  · have hc := Real.rpow_le_rpow_of_nonpos hS0 hMS (by linarith : 4 - (d : ℝ) ≤ 0)
    have he : S ^ (4 - (d : ℝ)) = (h t) ^ r := by
      dsimp only [S, r]
      rw [← Real.rpow_mul (hh t).le]
    rw [he] at hc
    have hL : 0 ≤ Real.log (1 / h t) := Real.log_nonneg (by apply (le_div_iff₀ (hh t)).mpr; simpa using hh1 t)
    exact (mul_le_mul_of_nonneg_left hc (mul_nonneg hC.le hL)).trans hF
  · have hbox : ((2 * M + 1 : ℕ) : ℝ) ≤ 3 * S := by push_cast; linarith
    have hp := pow_le_pow_left₀ (by positivity) hbox d
    have hm := mul_le_mul_of_nonneg_right hp (mul_nonneg hC.le (Real.rpow_nonneg (hh t).le (7 / 4 : ℝ)))
    have he : (3 * S) ^ d * (C * (h t) ^ (7 / 4 : ℝ)) =
        (C * (3 : ℝ) ^ d * (h t) ^ (1 / 2 : ℝ)) * h t := by
      rw [mul_pow]
      have hSd : S ^ d = (h t) ^ (-1 / 4 : ℝ) := by
        dsimp only [S]
        rw [← Real.rpow_mul_natCast (hh t).le]
        congr 1
        dsimp only [a]
        field_simp
      rw [hSd]
      have hhpow : (h t) ^ (-1 / 4 : ℝ) * (h t) ^ (7 / 4 : ℝ) = (h t) ^ (1 / 2 : ℝ) * h t := by
        calc (h t) ^ (-1 / 4 : ℝ) * (h t) ^ (7 / 4 : ℝ)
          = (h t) ^ ((-1 / 4 : ℝ) + 7 / 4) := (Real.rpow_add (hh t) _ _).symm
          _ = (h t) ^ ((1 / 2 : ℝ) + 1) := by norm_num
          _ = (h t) ^ (1 / 2 : ℝ) * h t := by rw [Real.rpow_add (hh t), Real.rpow_one]
      calc (3 : ℝ) ^ d * (h t) ^ (-1 / 4 : ℝ) * (C * (h t) ^ (7 / 4 : ℝ))
        = (C * (3 : ℝ) ^ d) * ((h t) ^ (-1 / 4 : ℝ) * (h t) ^ (7 / 4 : ℝ)) := by ring
        _ = _ := by rw [hhpow]; ring
    rw [he] at hm
    have hb := mul_le_mul_of_nonneg_right hS (hh t).le
    exact hm.trans (by nlinarith [hb])

end Parking
