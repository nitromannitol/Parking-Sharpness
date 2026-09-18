import Parking.Support.PinnedSceneryField
import Parking.Support.ProductFinite
import Parking.Support.SubgaussianMoment

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

/-- The initial-field Gaussian bound is uniform in an arbitrarily large prescribed hole capacity. -/
theorem exists_pinnedSparseBoxField_subgaussian (hd : 5 ≤ d) :
    ∃ V : ℝ≥0, 0 < V ∧ ∀ (ν : Measure ℤ) [IsProbabilityMeasure ν]
      (S : Finset (Site d)) (v : Site d) (a : ℤ), a ≤ 0 → ∀ (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d),
      HasSubgaussianMGF (fun ξ : S → ℤ => matchedMeanU (pinnedSparseBoxField S v a ξ) ρ T x -
        ∫ ζ, matchedMeanU (pinnedSparseBoxField S v a ζ) ρ T x ∂(Measure.pi (fun _ : S => ν))) V
          (Measure.pi (fun _ : S => ν)) := by
  classical
  obtain ⟨C, hC, hCb⟩ := fullGreen_bubble_bound hd
  let V : ℝ≥0 := ⟨4 * C, by positivity⟩
  refine ⟨V, by exact_mod_cast (show 0 < 4 * C by positivity), fun ν hν S v a ha ρ T x => ?_⟩
  let f : (S → ℤ) → ℝ := fun ξ => matchedMeanU (pinnedSparseBoxField S v a ξ) ρ T x
  have hfm : Measurable f := measurable_from_countable' _
  have hB := pinnedSparseBoxField_mean_bound (by omega : 1 ≤ d) S v a ha (ρ := ρ) (T := T) (x := x)
  refine ⟨fun t => integrable_exp_centered_bounded _ f hfm _ hB t _, fun t => ?_⟩
  have hb := mgf_bounded_differences_finite ν f hfm _ hB
    (fun w : S => 2 * fullGreen d (w.val - x))
    (fun w => mul_nonneg (by norm_num) (fullGreen_nonneg d _))
    (fun ξ w k => pinnedSparseBoxField_mean_oscillation (by omega) S v a ξ ρ T x w k) t
  have hsum : (∑ w : S, (2 * fullGreen d (w.val - x)) ^ 2) ≤ 4 * C := by
    have hs : Summable (fun y : Site d => fullGreen d (y - x) ^ 2) := by
      simpa only [pow_two] using (hCb x x).1
    have hsc : (∑' y : Site d, fullGreen d (y - x) ^ 2) ≤ C := by
      have h := (hCb x x).2
      simpa [pow_two, graphNorm] using h
    calc
      _ = 4 * ∑ w ∈ S, fullGreen d (w - x) ^ 2 := by
        rw [Finset.sum_coe_sort S (fun y => (2 * fullGreen d (y - x)) ^ 2)]
        simp_rw [mul_pow]
        rw [← Finset.mul_sum]
        norm_num
      _ ≤ 4 * ∑' y : Site d, fullGreen d (y - x) ^ 2 :=
        mul_le_mul_of_nonneg_left (hs.sum_le_tsum S (fun y _ => sq_nonneg _)) (by norm_num)
      _ ≤ 4 * C := mul_le_mul_of_nonneg_left hsc (by norm_num)
  exact hb.trans (Real.exp_le_exp.mpr (by change _ ≤ (4 * C) * t ^ 2 / 2; nlinarith [sq_nonneg t]))
end Parking
