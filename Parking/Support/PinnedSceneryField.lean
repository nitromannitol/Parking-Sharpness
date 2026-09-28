import Parking.Support.SceneryField
import Parking.Support.WeightedOdometerBounds

/-!
# Pinning one coordinate of the sparse box field

This file packages `sparseBoxField` with one coordinate `v` fixed to a prescribed
nonpositive value `a`, and transfers the coordinatewise particle bound and the
single-coordinate oscillation bound of `matchedMeanU` across that pinning. It pins only
one site at a time and otherwise reuses the bounds already proved for `sparseBoxField`.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A finite sparse field with one prescribed hole count. -/
def pinnedSparseBoxField (S : Finset (Site d)) (v : Site d) (a : ℤ) (ξ : S → ℤ) : Site d → ℤ :=
  Function.update (sparseBoxField S ξ) v a

/-- Pinning the coordinate at `v` to a nonpositive value `a` keeps every site's particle
count at most `1`, matching the bound already known for the unpinned `sparseBoxField`. -/
theorem pinnedSparseBoxField_particle_bound (S : Finset (Site d)) (v : Site d) (a : ℤ) (ha : a ≤ 0)
    (ξ : S → ℤ) (y : Site d) : (pinnedSparseBoxField S v a ξ y).toNat ≤ 1 := by
  classical
  by_cases hy : y = v
  · subst y; simp only [pinnedSparseBoxField, Function.update_self]; omega
  · simp only [pinnedSparseBoxField, Function.update_of_ne hy]
    have h := (sparseBoxField_bounds S ξ y).2
    omega

/-- The matched mean `matchedMeanU` of the pinned field obeys the same box-counting
bound `T * (2T + 1) ^ d` as any field with particle counts at most `1`, via
`matchedMeanU_le_box` applied to `pinnedSparseBoxField_particle_bound`. -/
theorem pinnedSparseBoxField_mean_bound (hd : 1 ≤ d) (S : Finset (Site d))
    (v : Site d) (a : ℤ) (ha : a ≤ 0) (ξ : S → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    |matchedMeanU (pinnedSparseBoxField S v a ξ) ρ T x| ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  rw [abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
  simpa only [mul_one] using
    matchedMeanU_le_box hd _ 1 (pinnedSparseBoxField_particle_bound S v a ha ξ) ρ T x

/-- Fixing one hole does not increase any other initial-coordinate oscillation. -/
theorem pinnedSparseBoxField_mean_oscillation (hd : 3 ≤ d) (S : Finset (Site d))
    (v : Site d) (a : ℤ) (ξ : S → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (w : S) (k : ℤ) :
    |matchedMeanU (pinnedSparseBoxField S v a ξ) ρ T x -
      matchedMeanU (pinnedSparseBoxField S v a (Function.update ξ w k)) ρ T x| ≤
        2 * fullGreen d (w.val - x) := by
  classical
  by_cases hw : w.val = v
  · have he : pinnedSparseBoxField S v a (Function.update ξ w k) =
        pinnedSparseBoxField S v a ξ := by
      unfold pinnedSparseBoxField
      rw [sparseBoxField_update, hw, Function.update_idem]
    rw [he, sub_self, abs_zero]
    exact mul_nonneg (by norm_num) (fullGreen_nonneg d _)
  · have he : pinnedSparseBoxField S v a (Function.update ξ w k) =
        Function.update (pinnedSparseBoxField S v a ξ) w.val (clipSparse k) := by
      unfold pinnedSparseBoxField
      rw [sparseBoxField_update]
      funext y
      by_cases hy : y = v
      · subst y; simp [Ne.symm hw]
      · by_cases hyw : y = w.val
        · subst y; simp [hw]
        · simp [hy, hyw]
    have h := matchedMeanU_update_abs_le hd (pinnedSparseBoxField S v a ξ) w.val ρ T x
      (pinnedSparseBoxField S v a ξ w.val) (clipSparse k)
    rw [Function.update_eq_self, ← he] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (fullGreen_nonneg d _)
    have hval : pinnedSparseBoxField S v a ξ w.val = sparseBoxField S ξ w.val :=
      Function.update_of_ne hw _ _
    rw [hval]
    have hb := sparseBoxField_bounds S ξ w.val
    have hk := clipSparse_bounds k
    have hbR : (-1 : ℝ) ≤ (sparseBoxField S ξ w.val : ℝ) ∧ (sparseBoxField S ξ w.val : ℝ) ≤ 1 := by
      exact_mod_cast hb
    have hkR : (-1 : ℝ) ≤ (clipSparse k : ℝ) ∧ (clipSparse k : ℝ) ≤ 1 := by exact_mod_cast hk
    exact abs_le.mpr ⟨by linarith, by linarith⟩
end Parking
