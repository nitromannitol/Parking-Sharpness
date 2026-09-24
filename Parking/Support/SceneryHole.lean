import Parking.Support.HoleRelative
import Parking.Support.ClippedTable

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Adding to a coordinate update gives the next integer value at that coordinate. -/
theorem addParticle_update (η : Site d → ℤ) (v : Site d) (k : ℤ) :
    addParticle v (Function.update η v k) = Function.update η v (k + 1) := by
  funext y
  by_cases hy : y = v
  · subst y; simp [addParticle]
  · simp [addParticle, hy]

/-- Two successive one-particle comparisons control all three sparse values. -/
theorem matchedMeanH_sparse_update_relative (hd : 3 ≤ d) (η : Site d → ℤ) (v x : Site d)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (k : ℤ) (hk : -1 ≤ k ∧ k ≤ 1) :
    escapePotential d x v ^ 2 * matchedMeanH (Function.update η v (-1)) ρ T x ≤
        matchedMeanH (Function.update η v k) ρ T x ∧
      matchedMeanH (Function.update η v k) ρ T x ≤ matchedMeanH (Function.update η v (-1)) ρ T x := by
  let e := escapePotential d x v
  let a := matchedMeanH (Function.update η v (-1)) ρ T x
  let b := matchedMeanH (Function.update η v 0) ρ T x
  let c := matchedMeanH (Function.update η v 1) ρ T x
  have he : 0 ≤ e ∧ e ≤ 1 := escapePotential_bounds hd x v
  have ha : 0 ≤ a := matchedMeanH_nonneg _ _ _ _
  have hb : e * a ≤ b ∧ b ≤ a := by
    have h := matchedMeanH_addParticle_relative hd (Function.update η v (-1)) v x ρ T
    simpa only [addParticle_update, neg_add_cancel] using h
  have hc : e * b ≤ c ∧ c ≤ b := by
    have h := matchedMeanH_addParticle_relative hd (Function.update η v 0) v x ρ T
    simpa only [addParticle_update, zero_add] using h
  have hsq : e ^ 2 ≤ e := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hb.1 he.1
  have hka : e ^ 2 * a ≤ a := (mul_le_mul_of_nonneg_right (hsq.trans he.2) ha).trans_eq (one_mul a)
  rcases hk with ⟨hklo, hkhi⟩
  interval_cases k
  · exact ⟨hka, le_rfl⟩
  · exact ⟨(mul_le_mul_of_nonneg_right hsq ha).trans hb.1, hb.2⟩
  · exact ⟨by nlinarith [hmul, hc.1], hc.2.trans hb.2⟩

/-- Clipping commutes with a coordinate update. -/
theorem clippedField_update (η : Site d → ℤ) (v : Site d) (k : ℤ) :
    clippedField (Function.update η v k) = Function.update (clippedField η) v (clipSparse k) := by
  funext y
  by_cases hy : y = v
  · subst y; simp [clippedField]
  · simp [clippedField, hy]

/-- Every clipped future hole mean is bounded by one. -/
theorem clippedMeanH_bounds (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    0 ≤ matchedMeanH (clippedField η) ρ T x ∧ matchedMeanH (clippedField η) ρ T x ≤ 1 := by
  refine ⟨matchedMeanH_nonneg _ _ _ _, (matchedMeanH_le_initial hd _ _ _ _).trans ?_⟩
  have h : (-clippedField η x).toNat ≤ 1 := by
    have hb := (clipSparse_bounds (η x)).1
    change (-clipSparse (η x)).toNat ≤ 1
    omega
  exact_mod_cast h
end Parking
