import Parking.Support.MeanLocality
import Parking.Support.MatchedUniform

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Restrict an integer count to the three possible sparse-law values. -/
def clipSparse (k : ℤ) : ℤ := max (-1) (min 1 k)

theorem clipSparse_bounds (k : ℤ) : -1 ≤ clipSparse k ∧ clipSparse k ≤ 1 := by
  unfold clipSparse
  omega

theorem clipSparse_eq {k : ℤ} (hk : -1 ≤ k ∧ k ≤ 1) : clipSparse k = k := by
  unfold clipSparse
  omega

/-- A bounded field determined by finitely many integer coordinates. -/
def sparseBoxField (S : Finset (Site d)) (ξ : S → ℤ) (y : Site d) : ℤ :=
  if hy : y ∈ S then clipSparse (ξ ⟨y, hy⟩) else 0

theorem sparseBoxField_bounds (S : Finset (Site d)) (ξ : S → ℤ) (y : Site d) :
    -1 ≤ sparseBoxField S ξ y ∧ sparseBoxField S ξ y ≤ 1 := by
  unfold sparseBoxField
  split
  · exact clipSparse_bounds _
  · omega

theorem sparseBoxField_update (S : Finset (Site d)) (ξ : S → ℤ) (v : S) (k : ℤ) :
    sparseBoxField S (Function.update ξ v k) = Function.update (sparseBoxField S ξ) v.val (clipSparse k) := by
  classical
  ext y
  by_cases hyv : y = v.val
  · subst y
    simp [sparseBoxField, v.property]
  · by_cases hy : y ∈ S
    · have hv : (⟨y, hy⟩ : S) ≠ v := fun he => hyv (congrArg Subtype.val he)
      simp [sparseBoxField, hy, hyv, hv]
    · simp [sparseBoxField, hy, hyv]

/-- Conditional mean odometers of bounded finite fields have a deterministic bound. -/
theorem sparseBoxField_mean_bound (hd : 1 ≤ d) (S : Finset (Site d)) (ξ : S → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    |matchedMeanU (sparseBoxField S ξ) ρ T x| ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  rw [abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
  have hη : ∀ y, (sparseBoxField S ξ y).toNat ≤ 1 := by
    intro y
    have h := (sparseBoxField_bounds S ξ y).2
    omega
  have h := integral_mono (integrable_matchedOdometer hd _ _ _ _)
    (integrable_const ((T * (2 * T + 1) ^ d : ℕ) : ℝ))
    (fun σ => Nat.cast_le.mpr (by simpa using matchedOdometer_le_box (sparseBoxField S ξ) 1 hη ρ σ T x))
  simpa only [matchedMeanU, integral_const, probReal_univ, one_smul] using h

/-- Changing one sparse initial count has oscillation at most twice the Green function. -/
theorem sparseBoxField_mean_oscillation (hd : 3 ≤ d) (S : Finset (Site d)) (ξ : S → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (v : S) (k : ℤ) :
    |matchedMeanU (sparseBoxField S ξ) ρ T x -
      matchedMeanU (sparseBoxField S (Function.update ξ v k)) ρ T x| ≤ 2 * fullGreen d (v.val - x) := by
  rw [sparseBoxField_update]
  have h := matchedMeanU_update_abs_le hd (sparseBoxField S ξ) v.val ρ T x
    (sparseBoxField S ξ v.val) (clipSparse k)
  rw [Function.update_eq_self] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (fullGreen_nonneg d _)
  have hb := sparseBoxField_bounds S ξ v.val
  have hk := clipSparse_bounds k
  have hbR : (-1 : ℝ) ≤ (sparseBoxField S ξ v.val : ℝ) ∧ (sparseBoxField S ξ v.val : ℝ) ≤ 1 := by exact_mod_cast hb
  have hkR : (-1 : ℝ) ≤ (clipSparse k : ℝ) ∧ (clipSparse k : ℝ) ≤ 1 := by exact_mod_cast hk
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end Parking
