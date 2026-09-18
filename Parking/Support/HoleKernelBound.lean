import Parking.Support.HoleKernel

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Finite scenery and instruction interaction weights satisfy the same Green bubble decay. -/
theorem exists_holeKernel_sum_bound (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x z : Site d) (S : Finset (Site d)),
      (∑ y ∈ S, (1 - escapePotential d x y) * (1 - escapePotential d z y)) ≤
        C * (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)) ∧
      (∑ y ∈ S, holeKernel d x z y) ≤
        C * (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := fullGreen_bubble_bound hd
  have hd3 : 3 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hq (x y : Site d) : 1 - escapePotential d x y ≤ fullGreen d (y - x) := by
    simp only [escapePotential, sub_sub_cancel]
    have hg : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd3)
    apply (div_le_iff₀ hg).mpr
    nlinarith [mul_nonneg (fullGreen_nonneg d (y - x)) (sub_nonneg.mpr (one_le_escapeConst hd3))]
  have hfinite (x z : Site d) (S : Finset (Site d)) :
      (∑ y ∈ S, (1 - escapePotential d x y) * (1 - escapePotential d z y)) ≤
        C * (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)) := by
    apply (Finset.sum_le_sum (fun y _ => mul_le_mul (hq x y) (hq z y)
      (sub_nonneg.mpr (escapePotential_bounds hd3 z y).2) (fullGreen_nonneg d _))).trans
    exact ((hb x z).1.sum_le_tsum S (fun y _ => mul_nonneg (fullGreen_nonneg d _) (fullGreen_nonneg d _))).trans (hb x z).2
  refine ⟨C, hC, fun x z S => ⟨hfinite x z S, ?_⟩⟩
  have he (a : Fin d × Bool) (w y : Site d) :
      escapePotential d w (y + stepVec a) = escapePotential d (w - stepVec a) y := by
    unfold escapePotential
    congr 3
    abel
  have hstep (a : Fin d × Bool) :
      (∑ y ∈ S, (1 - escapePotential d x (y + stepVec a)) * (1 - escapePotential d z (y + stepVec a))) ≤
        C * (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)) := by
    simp only [he]
    have h := hfinite (x - stepVec a) (z - stepVec a) S
    rw [show x - stepVec a - (z - stepVec a) = x - z by abel] at h
    exact h
  have h := integral_mono (integrable_step_fun hd1 _) (integrable_const _) hstep
  rw [integral_finsetSum _ (fun y _ => integrable_step_fun hd1 _)] at h
  simpa only [holeKernel, integral_const, probReal_univ, one_smul] using h
end Parking
