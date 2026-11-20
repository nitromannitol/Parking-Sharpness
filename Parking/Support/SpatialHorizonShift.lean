import Parking.Support.SpatialStabilityShifted
import Parking.Support.SpatialValueLocal
import Parking.Support.OrientedHorizonShift

/-!
# Removing the discrete horizon shift for the simple random walk

Uniform continuity of the reward on a compact space-time box controls the error from reading
the reward at the elapsed time shifted by the floor correction, and the maximal displacement
bound for the rescaled walk controls the complementary spatial tail.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The floor correction changes the spatial stopping values by a quantity tending to zero for
every bounded continuous reward. -/
theorem stoppingSup_horizonShift_tendsto_zero {d : ℕ} (hd : 1 ≤ d) {T M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (G : ℝ → (Fin d → ℝ) → ℝ)
    (hG : Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2))
    (hGM : ∀ s y, |G s y| ≤ M) :
    Tendsto (fun n : ℕ =>
      stoppingSup d (fun k z => G ((k : ℝ) / n) (spatialScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0 -
      stoppingSup d
          (fun k z => G ((k : ℝ) / n + orientedHorizonShift n T) (spatialScaledSite n z))
          ⌊(n : ℝ) * T⌋₊ 0) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail : Tendsto (fun A : ℝ => 2 * M * ((d : ℝ) ^ 2 * T / A ^ 2)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun A : ℝ => (2 * M * ((d : ℝ) ^ 2 * T)) / A ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    convert hdiv using 1
    funext A
    ring
  have hevent : ∀ᶠ A : ℝ in atTop, 0 < A ∧ 2 * M * ((d : ℝ) ^ 2 * T / A ^ 2) < ε / 2 :=
    (eventually_gt_atTop 0).and (htail.eventually (eventually_lt_nhds (by linarith)))
  obtain ⟨A, hA, hAtail⟩ := hevent.exists
  let S : Set (ℝ × (Fin d → ℝ)) := Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall 0 A
  have huc : UniformContinuousOn (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) S :=
    (isCompact_Icc.prod (isCompact_closedBall 0 A)).uniformContinuousOn_of_continuous
      hG.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (by linarith)
  have hmesh : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ := by
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
      simpa [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    exact ht.eventually (eventually_lt_nhds hδ)
  refine eventually_atTop.mp ?_
  filter_upwards [hmesh, eventually_ge_atTop 1] with n hnmesh hn
  have hn0 : 0 < n := by omega
  let F : ℕ → Site d → ℝ := fun k z => G ((k : ℝ) / n) (spatialScaledSite n z)
  let F' : ℕ → Site d → ℝ := fun k z =>
    G ((k : ℝ) / n + orientedHorizonShift n T) (spatialScaledSite n z)
  have hlocal : ∀ p ∉ spatialScaledExit d n T A, ∀ k ≤ ⌊(n : ℝ) * T⌋₊,
      |F k (walkPath 0 p k) - F' k (walkPath 0 p k)| ≤ ε / 2 := by
    intro p hp k hk
    let y := spatialScaledSite n (walkPath (0 : Site d) p k)
    have hy : ‖y‖ < A := by
      by_contra h
      exact hp ⟨k, hk, le_of_not_gt h⟩
    have htime := orientedHorizonShift_time_mem hn0 hT hk
    have hy' : y ∈ Metric.closedBall (0 : Fin d → ℝ) A := mem_closedBall_zero_iff.mpr hy.le
    have hdist : dist (((k : ℝ) / n, y) : ℝ × (Fin d → ℝ))
        (((k : ℝ) / n + orientedHorizonShift n T, y) : ℝ × (Fin d → ℝ)) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, dist_self, max_eq_left (abs_nonneg _)]
      have hs := orientedHorizonShift_bounds hn0 hT
      have heq : (k : ℝ) / n - ((k : ℝ) / n + orientedHorizonShift n T) =
          -orientedHorizonShift n T := by ring
      rw [heq, abs_neg, abs_of_nonneg hs.1]
      exact lt_of_le_of_lt hs.2 hnmesh
    have hv := hmod _ ⟨htime.1, hy'⟩ _ ⟨htime.2, hy'⟩ hdist
    rw [Real.dist_eq] at hv
    exact hv.le
  have hv := abs_stoppingSup_sub_le_of_local_reward hd (n := n) (T := T) (A := A)
    (by linarith : 0 ≤ ε / 2) F F' (fun k z => hGM _ _) (fun k z => hGM _ _) hlocal
  have hp := measureReal_spatialScaledExit_le hd hn hT hA
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * M by positivity)
  rw [Real.dist_eq, sub_zero]
  change |stoppingSup d F ⌊(n : ℝ) * T⌋₊ 0 - stoppingSup d F' ⌊(n : ℝ) * T⌋₊ 0| < ε
  linarith

end Parking
