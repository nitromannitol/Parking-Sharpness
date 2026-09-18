import Parking.Support.SceneryField
import Parking.Support.ProductFinite
import Parking.Support.SubgaussianMoment

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

/-- Square-summable Green influences give a uniform Gaussian bound for every finite scenery. -/
theorem exists_sparseBoxField_subgaussian (hd : 5 ≤ d) :
    ∃ V : ℝ≥0, 0 < V ∧ ∀ (ν : Measure ℤ) [IsProbabilityMeasure ν]
      (S : Finset (Site d)) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d),
      HasSubgaussianMGF (fun ξ : S → ℤ => matchedMeanU (sparseBoxField S ξ) ρ T x -
        ∫ ζ, matchedMeanU (sparseBoxField S ζ) ρ T x ∂(Measure.pi (fun _ : S => ν))) V
          (Measure.pi (fun _ : S => ν)) := by
  classical
  obtain ⟨C, hC, hCb⟩ := fullGreen_bubble_bound hd
  let V : ℝ≥0 := ⟨4 * C, by positivity⟩
  refine ⟨V, by exact_mod_cast (show 0 < 4 * C by positivity), fun ν hν S ρ T x => ?_⟩
  let f : (S → ℤ) → ℝ := fun ξ => matchedMeanU (sparseBoxField S ξ) ρ T x
  have hfm : Measurable f := measurable_from_countable' _
  have hB := sparseBoxField_mean_bound (by omega : 1 ≤ d) S (ρ := ρ) (T := T) (x := x)
  refine ⟨fun t => integrable_exp_centered_bounded _ f hfm _ hB t _, fun t => ?_⟩
  have hb := mgf_bounded_differences_finite ν f hfm _ hB
    (fun v : S => 2 * fullGreen d (v.val - x))
    (fun v => mul_nonneg (by norm_num) (fullGreen_nonneg d _))
    (fun ξ v k => sparseBoxField_mean_oscillation (by omega) S ξ ρ T x v k) t
  have hsum : (∑ v : S, (2 * fullGreen d (v.val - x)) ^ 2) ≤ 4 * C := by
    have hs : Summable (fun y : Site d => fullGreen d (y - x) ^ 2) := by
      simpa only [pow_two] using (hCb x x).1
    have hsc : (∑' y : Site d, fullGreen d (y - x) ^ 2) ≤ C := by
      have h := (hCb x x).2
      simpa [pow_two, graphNorm] using h
    calc
      _ = 4 * ∑ v ∈ S, fullGreen d (v - x) ^ 2 := by
        rw [Finset.sum_coe_sort S (fun y => (2 * fullGreen d (y - x)) ^ 2)]
        simp_rw [mul_pow]
        rw [← Finset.mul_sum]
        norm_num
      _ ≤ 4 * ∑' y : Site d, fullGreen d (y - x) ^ 2 :=
        mul_le_mul_of_nonneg_left (hs.sum_le_tsum S (fun y _ => sq_nonneg _)) (by norm_num)
      _ ≤ 4 * C := mul_le_mul_of_nonneg_left hsc (by norm_num)
  exact hb.trans (Real.exp_le_exp.mpr (by change _ ≤ (4 * C) * t ^ 2 / 2; nlinarith [sq_nonneg t]))
end Parking
