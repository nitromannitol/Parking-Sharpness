/-
Green-function identities and bubble decay for the nearest-hole estimates.
-/
import Parking.Support.GreenBridge
import Parking.Support.Range
import Parking.Support.GammaSum
import LatticeProb.Walk.GreenPointwise
import LatticeProb.Walk.HitProb

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem fullGreen_eq_srwGreenInf (d : ℕ) (x : Site d) :
    fullGreen d x = srwGreenInf d x := by
  unfold fullGreen srwGreenInf
  exact tsum_congr fun n => heat_eq_srwHeat d n x

theorem fullGreen_nonneg (d : ℕ) (x : Site d) : 0 ≤ fullGreen d x := by
  rw [fullGreen_eq_srwGreenInf]
  exact tsum_nonneg fun n => srwHeat_nonneg n x

theorem one_le_escapeConst (hd : 3 ≤ d) : 1 ≤ escapeConst d := by
  rw [escapeConst, fullGreen_eq_srwGreenInf]
  exact one_le_srwGreenInf_origin hd

theorem summable_fullGreen_sq (hd : 5 ≤ d) : Summable fun x : Site d => fullGreen d x ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 5 := ⟨d - 5, by omega⟩
  simpa only [fullGreen_eq_srwGreenInf] using summable_srwGreenInf_sq k

/-- The Green ratio is the probability of ever reaching the origin. -/
theorem fullGreen_div_escapeConst (hd : 3 ≤ d) (x : Site d) :
    fullGreen d x / escapeConst d = srwHitProb d x := by
  rw [escapeConst, fullGreen_eq_srwGreenInf, fullGreen_eq_srwGreenInf]
  exact (srwHitProb_eq_green_ratio hd x).symm

/-- The summable Green convolution has the spatial decay used by the two-hole bound. -/
theorem fullGreen_bubble_bound (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x z : Site d,
      (Summable fun y : Site d => fullGreen d (y - x) * fullGreen d (y - z)) ∧
      (∑' y : Site d, fullGreen d (y - x) * fullGreen d (y - z)) ≤
        C * (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 5 := ⟨d - 5, by omega⟩
  obtain ⟨C, hC, h⟩ := exists_tsum_srwGreenInf_mul_le k
  refine ⟨C, hC, fun x z => ?_⟩
  obtain ⟨hs, hb⟩ := h (x - z)
  let e : Site (k + 5) ≃ Site (k + 5) := Equiv.addRight (-x)
  have he (y : Site (k + 5)) : e y + (x - z) = y - z := by simp only [e, Equiv.coe_addRight]; abel
  have hfun : (fun y : Site (k + 5) => fullGreen (k + 5) (y - x) * fullGreen (k + 5) (y - z)) =
      (fun y => srwGreenInf (k + 5) y * srwGreenInf (k + 5) (y + (x - z))) ∘ e := by
    funext y
    rw [Function.comp_apply, he]
    simp only [fullGreen_eq_srwGreenInf, e, Equiv.coe_addRight, sub_eq_add_neg]
  have hsum : (∑' y : Site (k + 5), fullGreen (k + 5) (y - x) * fullGreen (k + 5) (y - z)) =
      ∑' y : Site (k + 5), srwGreenInf (k + 5) y * srwGreenInf (k + 5) (y + (x - z)) := by
    rw [hfun]
    exact e.tsum_eq (fun y : Site (k + 5) =>
      srwGreenInf (k + 5) y * srwGreenInf (k + 5) (y + (x - z)))
  constructor
  · rw [hfun]
    exact e.summable_iff.mpr hs
  · rw [hsum]
    convert hb using 1
    rw [show (4 : ℝ) - (k + 5 : ℕ) = -((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv, graphNorm_eq_srw]
end Parking
