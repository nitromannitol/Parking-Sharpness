import Parking.Support.SinkCenteredMoment
import Parking.Support.AverageMoment
import Parking.Support.SinkCompensatorMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Averaging the centered sink odometers gives the same moment scale for entrances. -/
theorem exists_sparseSinkLambda_centered_moment (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (r : ℝ), 2 ≤ r →
      rNorm ((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) r
        (fun z => sparseSinkLambda T z - walkOp (sparseSinkMean (d := d) p T) 0) ≤
          C * (Real.sqrt (r * (meanU (law d (threePointLaw p)) T + r)) + r) := by
  obtain ⟨C, hC, hbound⟩ := exists_sparseSink_centered_moment hBernstein hd
  refine ⟨C, hC, fun p hp hp4 T r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)
  let F : Site d → (Site d → ℤ) × FlatRoundNoise d → ℝ :=
    fun x z => sparseSinkTableU T 0 x z - sparseSinkMean p T x
  have hF (x : Site d) : Measurable (F x) := (measurable_sparseSinkTableU hd1 T 0 x).sub_const _
  have hFB (x : Site d) (z : (Site d → ℤ) × FlatRoundNoise d) :
      |F x z| ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) + |sparseSinkMean (d := d) p T x| :=
    (abs_sub _ _).trans (add_le_add (sparseSinkTableU_bound T 0 x z) (le_refl _))
  have hsum : ∑ _x ∈ nbrFinset (0 : Site d), (1 / (2 * (d : ℝ))) = 1 := by
    simp only [Finset.sum_const, Graph.Zd.card_nbrFinset, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  have h := rNorm_average_le μ (nbrFinset (0 : Site d)) (fun _ => 1 / (2 * (d : ℝ))) F
    (fun _ _ => by positivity) hsum (fun x _ => hF x) (by linarith : 1 ≤ r)
    (fun x _ => integrable_abs_rpow_bounded μ (F x) (hF x) _ (hFB x) (by linarith))
    (C * (Real.sqrt (r * (meanU (law d (threePointLaw p)) T + r)) + r))
    (by positivity) (fun x _ => hbound p hp hp4 T 0 x r hr)
  have he (z : (Site d → ℤ) × FlatRoundNoise d) :
      (∑ x ∈ nbrFinset (0 : Site d), 1 / (2 * (d : ℝ)) * F x z) =
        sparseSinkLambda T z - walkOp (sparseSinkMean (d := d) p T) 0 := by
    simp only [F, sparseSinkLambda, walkOp_eq_nbrFinset, mul_sub, Finset.sum_sub_distrib,
      ← Finset.mul_sum, div_eq_inv_mul, mul_one]
  simpa only [he] using h.2
end Parking
