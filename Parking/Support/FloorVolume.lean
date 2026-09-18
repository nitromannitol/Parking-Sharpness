import Mathlib

noncomputable section
namespace Parking

/-- A lattice scale whose volume is comparable to the reciprocal density. -/
theorem exists_radius_volume (d : ℕ) (hd : 1 ≤ d) {b h : ℝ} (hb : 0 < b)
    (hh : 0 < h) (hhb : h ≤ b) :
    ∃ R : ℕ, b ≤ h * ((R + 1 : ℕ) : ℝ) ^ d ∧
      h * ((8 * d * R + 1 : ℕ) : ℝ) ^ d ≤ ((8 * d + 1 : ℕ) : ℝ) ^ d * b := by
  let S : ℝ := (b / h) ^ ((d : ℝ)⁻¹)
  have hS0 : 0 < S := Real.rpow_pos_of_pos (div_pos hb hh) _
  have hS1 : 1 ≤ S := Real.one_le_rpow (by apply (le_div_iff₀ hh).mpr; simpa using hhb) (by positivity)
  have hSd : S ^ d = b / h := Real.rpow_inv_natCast_pow (div_pos hb hh).le (by omega)
  let R := Nat.floor S
  have hR : (R : ℝ) ≤ S := Nat.floor_le hS0.le
  have hR1 : S ≤ (R : ℝ) + 1 := (Nat.lt_floor_add_one S).le
  refine ⟨R, ?_, ?_⟩
  · have h := pow_le_pow_left₀ hS0.le hR1 d
    rw [hSd] at h
    have hm := mul_le_mul_of_nonneg_left h hh.le
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_cancel₀ b hh.ne'] using hm
  · have hv : ((8 * d * R + 1 : ℕ) : ℝ) ≤ ((8 * d + 1 : ℕ) : ℝ) * S := by
      push_cast
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity) hv d
    rw [mul_pow, hSd] at hp
    have hm := mul_le_mul_of_nonneg_left hp hh.le
    calc h * ((8 * d * R + 1 : ℕ) : ℝ) ^ d
      ≤ h * (((8 * d + 1 : ℕ) : ℝ) ^ d * (b / h)) := hm
      _ = ((8 * d + 1 : ℕ) : ℝ) ^ d * b := by field_simp

end Parking
