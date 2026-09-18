import Parking.Support.SinkNoArrival
import Parking.Support.HoleBounds
import Parking.Support.LogFromTail
import Parking.Support.CriticalMeanDiverges

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology
variable {d : ℕ}

/-- Sparse hole survival decays exponentially in the mean odometer, uniformly in p. -/
theorem exists_sparse_hole_exp_bound (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ T : ℕ,
      holeProb d (threePointLaw p) T ≤ A * Real.exp (-c * meanU (law d (threePointLaw p)) T) := by
  obtain ⟨A, c, hA, hc, hb⟩ := exists_sparseSink_noArrival_bound hBernstein hd
  refine ⟨A, c, hA, hc, fun p hp hp4 T => ?_⟩
  rw [holeProb_eq_mul_sink_noArrival (by omega) hp hp4 T]
  have h := mul_le_mul_of_nonneg_left (hb p hp hp4 T) hp.le
  exact h.trans (mul_le_of_le_one_left (by positivity) (by linarith))

/-- The logarithmic mean estimate has a constant bound before the sparse parameter. -/
theorem exists_sparse_mean_log_bound (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ T : ℕ,
      meanU (law d (threePointLaw p)) T ≤ C * Real.log (1 / holeProb d (threePointLaw p) T) := by
  obtain ⟨A, c, hA, hc, hb⟩ := exists_sparse_hole_exp_bound hBernstein hd
  obtain ⟨C, hC, hlog⟩ := exists_log_bound_of_exp hA hc
  refine ⟨C, hC, fun p hp hp4 T => ?_⟩
  exact hlog _ _ (holeProb_pos (by omega) hp hp4 T)
    ((holeProb_le_p (by omega) hp hp4 T).trans hp4) (hb p hp hp4 T)

/-- Critical sparse holes vanish in the limit. -/
theorem sparse_holeProb_tendsto_zero (hBernstein : External.Bernstein) (hd : 5 ≤ d)
    {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) :
    Tendsto (holeProb d (threePointLaw p)) atTop (𝓝 0) := by
  obtain ⟨A, c, _, hc, hb⟩ := exists_sparse_hole_exp_bound hBernstein hd
  have hν := criticalLaw_threePointLaw hp (by linarith : 2 * p ≤ 1)
  haveI := hν.prob
  have hmean := meanU_tendsto_atTop (d := d) (by omega) (threePointLaw p) hν.nonconst
    (integrable_threePointLaw p _) hν.mean
  have hneg : Tendsto (fun T => -c * meanU (law d (threePointLaw p)) T) atTop atBot := by
    apply tendsto_atBot.mpr
    intro B
    filter_upwards [hmean.eventually (eventually_ge_atTop (-B / c))] with T hT
    have h := (div_le_iff₀ hc).mp hT
    linarith
  have he : Tendsto (fun T => A * Real.exp (-c * meanU (law d (threePointLaw p)) T)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (Real.tendsto_exp_atBot.comp hneg).const_mul A
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) (hb p hp hp4) he
end Parking
