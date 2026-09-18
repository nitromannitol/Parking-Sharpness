import Parking.Support.SinkNoiseMoment
import Parking.Support.SinkSceneryLaw
import Parking.Support.CenteredProductMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Every sink odometer has the centered moment scale needed for a lower-tail estimate. -/
theorem exists_sparseSink_centered_moment (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (v x : Site d) (r : ℝ), 2 ≤ r →
      rNorm ((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) r
        (fun z => sparseSinkTableU T v x z -
          ∫ η, matchedMeanU (sparseSinkField T v η) 0 T x ∂(iidLaw d (threePointLaw p))) ≤
          C * (Real.sqrt (r * (meanU (law d (threePointLaw p)) T + r)) + r) := by
  obtain ⟨Cb, hCb, hb⟩ := exists_sparseSink_noise_moment hBernstein hd
  obtain ⟨Cs, hCs, hs⟩ := exists_sparseSink_scenery_moment hd
  refine ⟨Cb + Cs, by linarith, fun p hp hp4 T v x r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd1
  let μ := iidLaw d (threePointLaw p)
  let Y : (Site d → ℤ) → ℝ := fun η => matchedMeanU (sparseSinkField T v η) 0 T x
  let b := ∫ η, Y η ∂μ
  let B : ℝ := ((T * (2 * T + 1) ^ d : ℕ) : ℝ)
  have hY : Measurable Y := (measurable_matchedMeanU hd1 0 T x).comp (measurable_sparseSinkField T v)
  have hYB (η : Site d → ℤ) : |Y η| ≤ B := by
    rw [abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
    simpa only [mul_one] using matchedMeanU_le_box hd1 _ 1 (sparseSinkField_particle_bound T v η) 0 T x
  have hdec := rNorm_bounded_centered_decomposition μ (flatRoundNoiseLaw d) (sparseSinkTableU T v x) Y
    (measurable_sparseSinkTableU hd1 T v x) hY B B (sparseSinkTableU_bound T v x) hYB b (by linarith : 1 ≤ r)
  have hsc := hs (threePointLaw p) T v x r hr
  have hno := hb p hp hp4 T v x r hr
  have hsr : Real.sqrt r ≤ Real.sqrt (r * (meanU (law d (threePointLaw p)) T + r)) := by
    apply Real.sqrt_le_sqrt
    have hm : 0 ≤ meanU (law d (threePointLaw p)) T := integral_nonneg fun _ => Nat.cast_nonneg _
    nlinarith
  have h := hdec.trans (add_le_add hsc hno)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hsr hCs.le, mul_nonneg hCs.le (by linarith : 0 ≤ r)])
end Parking
