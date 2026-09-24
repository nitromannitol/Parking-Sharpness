import Parking.Support.OnePointMoment
import Parking.Support.HoleTail

noncomputable section
namespace Parking
open MeasureTheory Filter Topology

/-- The complete sparse one-point estimates, with one dimension-only constant. -/
theorem nearest_one_point_proof (hBernstein : External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 →
      (∀ (t : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
          Integrable (fun ω => (U ω t x : ℝ) ^ r) (law d (threePointLaw p)) ∧
          (∫ ω, (U ω t x : ℝ) ^ r ∂(law d (threePointLaw p))) ^ (1 / r)
            ≤ C * (meanU (law d (threePointLaw p)) t + r)) ∧
      (∀ t : ℕ, meanU (law d (threePointLaw p)) t ≤ C * Real.log (1 / holeProb d (threePointLaw p) t)) ∧
      Antitone (holeProb d (threePointLaw p)) ∧ Tendsto (holeProb d (threePointLaw p)) atTop (𝓝 0) := by
  obtain ⟨Cu, hCu, hu⟩ := exists_sparse_odometer_moment_bound hBernstein hd
  obtain ⟨Cl, _, hl⟩ := exists_sparse_mean_log_bound hBernstein hd
  refine ⟨max Cu Cl, hCu.trans_le (le_max_left _ _), fun p hp hp4 => ?_⟩
  refine ⟨fun t x r hr => ?_, fun t => ?_, holeProb_antitone (by omega) hp hp4,
    sparse_holeProb_tendsto_zero hBernstein hd hp hp4⟩
  · obtain ⟨hi, hb⟩ := hu p hp hp4 t x r hr
    refine ⟨hi, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)⟩
    have hm : 0 ≤ meanU (law d (threePointLaw p)) t := integral_nonneg fun _ => Nat.cast_nonneg _
    linarith
  · apply (hl p hp hp4 t).trans
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    apply Real.log_nonneg
    apply (le_div_iff₀ (holeProb_pos (by omega) hp hp4 t)).mpr
    have h := holeProb_le_p (d := d) (by omega) hp hp4 t
    linarith
end Parking
