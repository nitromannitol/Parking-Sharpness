/- A uniform logarithmic square-norm bound up to a directed horizon. -/
import Parking.Support.OrientedGreenRates

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

theorem orientedGreen_sq_mono {m n : ℕ} (hmn : m ≤ n) :
    (∑' x : Site d, orientedGreen d m x ^ 2) ≤ ∑' x : Site d, orientedGreen d n x ^ 2 := by
  rw [tsum_orientedGreen_sq, tsum_orientedGreen_sq]
  exact sum_le_sum_of_subset_of_nonneg (range_mono hmn)
    (fun l _ _ => tsum_nonneg fun x => sq_nonneg _)

theorem exists_orientedGreen_sq_log_bound (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m ≤ n →
      (∑' x : Site d, orientedGreen d m x ^ 2) ≤ C * Real.log ((n : ℝ) + 1) := by
  by_cases hd3 : d = 3
  · subst d
    obtain ⟨c, C, _hc, hC, hb⟩ := exists_orientedGreen_three_sq_bounds
    exact ⟨C, hC, fun n hn m hmn => (orientedGreen_sq_mono hmn).trans (hb n hn).2⟩
  · obtain ⟨C, hC, hb⟩ := exists_orientedGreen_high_sq_bound (d := d) (by omega)
    refine ⟨2 * C, by positivity, fun n hn m hmn => ?_⟩
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ (n : ℝ) + 1 by linarith)
    have hlog : 1 ≤ 2 * Real.log ((n : ℝ) + 1) := by linarith [Real.log_two_gt_d9]
    have hmul := mul_le_mul_of_nonneg_left hlog hC.le
    calc (∑' x : Site d, orientedGreen d m x ^ 2) ≤ C :=
        (orientedGreen_sq_mono hmn).trans (hb n hn)
      _ ≤ _ := by nlinarith

end Parking
