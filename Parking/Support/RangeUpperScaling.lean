import Parking.Support.RangeConnected

/-!
# Scaling of the small-range estimate

A block length proportional to the square of a spatial scale controls the
heat-kernel factor for ranges of comparable volume.
-/

open LatticeProb

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A quadratic block length makes the heat-kernel factor small for a range of
at most twice the `d`-dimensional volume of the scale. -/
theorem exists_range_block_scale (hd : 1 ≤ d) : ∃ Q : ℕ, 1 ≤ Q ∧ ∀ m k : ℕ, 1 ≤ k →
    (m : ℝ) ≤ 2 * (k : ℝ) ^ d →
      (m : ℝ) * (Real.sqrt 2 ^ d * greenConst d *
        ((Q * k ^ 2 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
  let C : ℝ := Real.sqrt 2 ^ d * greenConst d
  have hC : 0 ≤ C := mul_nonneg (by positivity) (greenConst_nonneg d)
  obtain ⟨q, hq⟩ := exists_nat_ge ((4 * C) ^ 2)
  let Q := q + 1
  have hQ1 : (1 : ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQsq : (4 * C) ^ 2 ≤ (Q : ℝ) := by dsimp [Q]; push_cast; linarith
  have hQsqrt : 4 * C ≤ Real.sqrt (Q : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * C)]
    exact Real.sqrt_le_sqrt hQsq
  have hQpow : Real.sqrt (Q : ℝ) ≤ (Q : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hQfactor : (4 * C) * (Q : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 := by
    have hpow : 0 ≤ (Q : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hQpos.le _
    calc (4 * C) * (Q : ℝ) ^ (-(d : ℝ) / 2)
        ≤ (Q : ℝ) ^ ((d : ℝ) / 2) * (Q : ℝ) ^ (-(d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (hQsqrt.trans hQpow) hpow
      _ = 1 := by
        rw [← Real.rpow_add hQpos, show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
          Real.rpow_zero]
  refine ⟨Q, by dsimp [Q]; omega, fun m k hk hm => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkpow : (0 : ℝ) < (k : ℝ) ^ d := pow_pos hkpos _
  have hdec : (((Q * k ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2) =
      (Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹ := by
    push_cast
    rw [Real.mul_rpow hQpos.le (sq_nonneg _), ← Real.rpow_natCast (k : ℝ) 2,
      ← Real.rpow_mul hkpos.le]
    have he : ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) := by push_cast; ring
    rw [he, Real.rpow_neg hkpos.le, Real.rpow_natCast]
  rw [hdec]
  have hnonneg : 0 ≤ C * ((Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹) := by positivity
  calc (m : ℝ) * (C * ((Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹))
      ≤ (2 * (k : ℝ) ^ d) *
          (C * ((Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹)) :=
        mul_le_mul_of_nonneg_right hm hnonneg
    _ = ((4 * C) * (Q : ℝ) ^ (-(d : ℝ) / 2)) / 2 := by
      field_simp; ring
    _ ≤ 1 / 2 := by linarith

end Parking

end
