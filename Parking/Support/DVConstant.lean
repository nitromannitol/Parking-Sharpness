import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The Donsker-Varadhan constant

For `a, c ≥ 0` the least value of `a w + c w^{-2/d}` over `w > 0` is

  `dvConst d a c = ((d+2)/2 · a)^{2/(d+2)} ((d+2)/d · c)^{d/(d+2)}`

(`dvConst_le`, `exists_le_dvConst`), by the weighted inequality of arithmetic and geometric
means with weights `2/(d+2)` and `d/(d+2)`.  It is continuous in `(a, c)`.  With `c` the
Faber-Krahn constant of the walk, it is the constant `k` of the Donsker-Varadhan estimate.
-/

noncomputable section

namespace Parking

/-- `((d+2)/2 · a)^{2/(d+2)} ((d+2)/d · c)^{d/(d+2)}`. -/
def dvConst (d : ℕ) (a c : ℝ) : ℝ :=
  (((d : ℝ) + 2) / 2 * a) ^ ((2 : ℝ) / (d + 2)) * (((d : ℝ) + 2) / d * c) ^ ((d : ℝ) / (d + 2))

variable {d : ℕ}

theorem dvConst_nonneg {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ dvConst d a c := by
  unfold dvConst
  positivity

theorem continuous_dvConst (d : ℕ) : Continuous fun p : ℝ × ℝ => dvConst d p.1 p.2 := by
  unfold dvConst
  have h1 : (0 : ℝ) ≤ 2 / ((d : ℝ) + 2) := by positivity
  have h2 : (0 : ℝ) ≤ (d : ℝ) / ((d : ℝ) + 2) := by positivity
  exact ((Real.continuous_rpow_const h1).comp (continuous_const.mul continuous_fst)).mul
    ((Real.continuous_rpow_const h2).comp (continuous_const.mul continuous_snd))

/-- The geometric mean of the two terms does not depend on `w`. -/
theorem geom_mean_eq_dvConst (hd : 1 ≤ d) {a c w : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hw : 0 < w) :
    (((d : ℝ) + 2) / 2 * a * w) ^ ((2 : ℝ) / (d + 2))
        * (((d : ℝ) + 2) / d * c * w ^ (-(2 : ℝ) / d)) ^ ((d : ℝ) / (d + 2))
      = dvConst d a c := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : (((d : ℝ) + 2) / 2 * a * w) ^ ((2 : ℝ) / (d + 2))
      = (((d : ℝ) + 2) / 2 * a) ^ ((2 : ℝ) / (d + 2)) * w ^ ((2 : ℝ) / (d + 2)) :=
    Real.mul_rpow (by positivity) hw.le
  have hB : (((d : ℝ) + 2) / d * c * w ^ (-(2 : ℝ) / d)) ^ ((d : ℝ) / (d + 2))
      = (((d : ℝ) + 2) / d * c) ^ ((d : ℝ) / (d + 2))
        * (w ^ (-(2 : ℝ) / d)) ^ ((d : ℝ) / (d + 2)) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hC : (w ^ (-(2 : ℝ) / d)) ^ ((d : ℝ) / (d + 2)) = w ^ (-((2 : ℝ) / (d + 2))) := by
    rw [← Real.rpow_mul hw.le]
    congr 1
    field_simp
  have hD : w ^ ((2 : ℝ) / (d + 2)) * w ^ (-((2 : ℝ) / (d + 2))) = 1 := by
    rw [← Real.rpow_add hw, add_neg_cancel, Real.rpow_zero]
  rw [hA, hB, hC]
  unfold dvConst
  calc (((d : ℝ) + 2) / 2 * a) ^ ((2 : ℝ) / (d + 2)) * w ^ ((2 : ℝ) / (d + 2))
        * ((((d : ℝ) + 2) / d * c) ^ ((d : ℝ) / (d + 2)) * w ^ (-((2 : ℝ) / (d + 2))))
      = (((d : ℝ) + 2) / 2 * a) ^ ((2 : ℝ) / (d + 2))
          * (((d : ℝ) + 2) / d * c) ^ ((d : ℝ) / (d + 2))
          * (w ^ ((2 : ℝ) / (d + 2)) * w ^ (-((2 : ℝ) / (d + 2)))) := by ring
    _ = _ := by rw [hD, mul_one]

/-- **The inequality of means**: `dvConst d a c ≤ a w + c w^{-2/d}` for every `w > 0`. -/
theorem dvConst_le (hd : 1 ≤ d) {a c w : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hw : 0 < w) :
    dvConst d a c ≤ a * w + c * w ^ (-(2 : ℝ) / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (2 : ℝ) / (d + 2))
    (w₂ := (d : ℝ) / (d + 2)) (p₁ := ((d : ℝ) + 2) / 2 * a * w)
    (p₂ := ((d : ℝ) + 2) / d * c * w ^ (-(2 : ℝ) / d)) (by positivity) (by positivity)
    (by positivity) (by positivity) (by field_simp; ring)
  rw [geom_mean_eq_dvConst hd ha hc hw] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-- **The least value is attained, or approached when `c = 0`.** -/
theorem exists_le_dvConst (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) {ε : ℝ}
    (hε : 0 < ε) : ∃ w : ℝ, 0 < w ∧ a * w + c * w ^ (-(2 : ℝ) / d) ≤ dvConst d a c + ε := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rcases hc.eq_or_lt with hc0 | hcpos
  · subst hc0
    refine ⟨ε / (2 * a), by positivity, ?_⟩
    have h0 : dvConst d a 0 = 0 := by
      unfold dvConst
      rw [mul_zero, Real.zero_rpow (by positivity), mul_zero]
    rw [h0, zero_mul, add_zero, zero_add]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  · set w : ℝ := (2 * c / (a * d)) ^ ((d : ℝ) / (d + 2)) with hwdef
    have hw : 0 < w := by positivity
    refine ⟨w, hw, ?_⟩
    -- at `w` the two weighted terms are equal
    set p : ℝ := ((d : ℝ) + 2) / 2 * a * w with hp
    have hpw : ((d : ℝ) + 2) / d * c * w ^ (-(2 : ℝ) / d) = p := by
      have hw2 : w * w ^ ((2 : ℝ) / d) = 2 * c / (a * d) := by
        rw [hwdef, ← Real.rpow_one_add' (by positivity) (by positivity), ← Real.rpow_mul
          (by positivity)]
        have : (d : ℝ) / (d + 2) * (1 + 2 / d) = 1 := by field_simp
        rw [this, Real.rpow_one]
      rw [show -(2 : ℝ) / d = -((2 : ℝ) / d) by ring, Real.rpow_neg hw.le, hp]
      have hwp : 0 < w ^ ((2 : ℝ) / d) := Real.rpow_pos_of_pos hw _
      have h3 : a * d * (w * w ^ ((2 : ℝ) / d)) = 2 * c := by
        rw [hw2]; field_simp
      field_simp
      nlinarith
    have hmean := geom_mean_eq_dvConst hd ha.le hc hw
    rw [hpw, ← hp, ← Real.rpow_add (by positivity)] at hmean
    have h1 : (2 : ℝ) / (d + 2) + d / (d + 2) = 1 := by field_simp; ring
    rw [h1, Real.rpow_one] at hmean
    have e1 : (2 : ℝ) / (d + 2) * p = a * w := by rw [hp]; field_simp
    have e2 : (d : ℝ) / (d + 2) * (((d : ℝ) + 2) / d * c * w ^ (-(2 : ℝ) / d))
        = c * w ^ (-(2 : ℝ) / d) := by field_simp
    have hsum : a * w + c * w ^ (-(2 : ℝ) / d)
        = (2 : ℝ) / (d + 2) * p + (d : ℝ) / (d + 2) * p := by
      rw [← e1, ← e2, hpw]
    rw [hsum, ← add_mul, h1, one_mul, hmean]
    linarith

end Parking

end
