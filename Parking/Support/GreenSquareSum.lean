import Parking.Support.NearestGreen
import Parking.Support.RoundHitting
import Parking.Support.GreenPotential

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The neighbor average of the squared Green function is nonnegative. -/
theorem greenSquareWeight_nonneg (x v : Site d) :
    0 ≤ walkOp (fun y => fullGreen d (y - x) ^ 2) v := by
  unfold walkOp nbrSum
  positivity

/-- The total weight PG² over any finite set is bounded by the dimension-only bubble constant. -/
theorem exists_greenSquareWeight_sum_bound (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Site d) (S : Finset (Site d)),
      (∑ v ∈ S, walkOp (fun y => fullGreen d (y - x) ^ 2) v) ≤ C := by
  classical
  obtain ⟨C, hC, hCb⟩ := fullGreen_bubble_bound hd
  refine ⟨C, hC, fun x S => ?_⟩
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hfinite (a : Fin d × Bool) : ∑ v ∈ S, fullGreen d (v + stepVec a - x) ^ 2 ≤ C := by
    have hs : Summable (fun y : Site d => fullGreen d (y - (x - stepVec a)) ^ 2) := by
      simpa only [pow_two] using (hCb (x - stepVec a) (x - stepVec a)).1
    have hc : (∑' y : Site d, fullGreen d (y - (x - stepVec a)) ^ 2) ≤ C := by
      simpa [pow_two, graphNorm] using (hCb (x - stepVec a) (x - stepVec a)).2
    have he : (fun v : Site d => fullGreen d (v + stepVec a - x) ^ 2) =
        (fun v => fullGreen d (v - (x - stepVec a)) ^ 2) := by
      funext v
      congr 2
      abel
    rw [he]
    exact (hs.sum_le_tsum S (fun _ _ => sq_nonneg _)).trans hc
  have hi (v : Site d) : Integrable (fun a : Fin d × Bool => fullGreen d (v + stepVec a - x) ^ 2) (stepLaw d) := by
    apply Integrable.of_bound (measurable_from_countable' _).aestronglyMeasurable (escapeConst d ^ 2)
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (fullGreen_nonneg d _) (fullGreen_le_escapeConst (by omega) _) 2
  have he : (∑ v ∈ S, walkOp (fun y => fullGreen d (y - x) ^ 2) v) =
      ∫ a, (∑ v ∈ S, fullGreen d (v + stepVec a - x) ^ 2) ∂(stepLaw d) := by
    rw [integral_finsetSum _ (fun v _ => hi v)]
    exact Finset.sum_congr rfl fun v _ => (integral_stepLaw_add hd1 (fun y => fullGreen d (y - x) ^ 2) v).symm
  rw [he]
  have h := integral_mono (integrable_finsetSum _ (fun v _ => hi v)) (integrable_const C) hfinite
  simpa only [integral_const, probReal_univ, one_smul] using h
end Parking
