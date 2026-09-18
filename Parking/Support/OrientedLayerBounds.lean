/- Two-sided directed layer norms from the ordinary walk's diagonal bounds. -/
import Parking.Support.OrientedCollision
import Parking.Support.BinomialNorm
import LatticeProb.Walk.SRWDiag

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

theorem exists_orientedLayer_sq_bounds (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      c / Real.sqrt n ^ (d - 1) ≤ ∑' x : Site d, orientedLayer d n x ^ 2 ∧
        (∑' x : Site d, orientedLayer d n x ^ 2) ≤ C / Real.sqrt n ^ (d - 1) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_srwHeat_diag_bounds (d := d) (by omega)
  refine ⟨c, 4 * C, hc, by positivity, fun n hn => ?_⟩
  let s := Real.sqrt (n : ℝ)
  let t := Real.sqrt ((n : ℝ) + 1)
  let q := conv n 0
  let S := ∑' x : Site d, orientedLayer d n x ^ 2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have hts : t ≤ 2 * s := by
    have hs2 : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have ht2 : t ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    nlinarith
  have hq : 0 ≤ q := conv_nonneg n 0
  have hqtlo : (1 / 2 : ℝ) ≤ q * t := (div_le_iff₀ ht).mp (conv_zero_lower n)
  have hqthi : q * t ≤ 1 := (le_div_iff₀ ht).mp (conv_zero_upper n)
  have hqslo : (1 / 4 : ℝ) ≤ q * s := by
    have h := mul_le_mul_of_nonneg_left hts hq
    nlinarith
  have hqshi : q * s ≤ 1 := (mul_le_mul_of_nonneg_left hst hq).trans hqthi
  have hS : 0 ≤ S := tsum_nonneg fun x => sq_nonneg _
  have hpow : s ^ d = s ^ (d - 1) * s := by
    have he : d = (d - 1) + 1 := by omega
    conv_lhs => rw [he]
    exact pow_succ s (d - 1)
  have he : (q * S) * s ^ d = (q * s) * (s ^ (d - 1) * S) := by rw [hpow]; ring
  have hl := (div_le_iff₀ (pow_pos hs d)).mp (hb n hn).1
  have hu := (le_div_iff₀ (pow_pos hs d)).mp (hb n hn).2
  rw [orientedLayer_collision_identity] at hl hu
  change c ≤ (q * S) * s ^ d at hl
  change (q * S) * s ^ d ≤ C at hu
  rw [he] at hl hu
  have hW : 0 ≤ s ^ (d - 1) * S := mul_nonneg (pow_nonneg hs.le _) hS
  constructor
  · apply (div_le_iff₀ (pow_pos hs (d - 1))).mpr
    have h := mul_le_mul_of_nonneg_right hqshi hW
    nlinarith
  · apply (le_div_iff₀ (pow_pos hs (d - 1))).mpr
    have h := mul_le_mul_of_nonneg_right hqslo hW
    nlinarith

end Parking
