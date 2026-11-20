import Parking.Support.OrientedStabilityShifted
import Parking.Support.OrientedValueLocal

/-!
# Removing the discrete horizon shift

Uniform continuity on a compact space-time box controls the floor error. A
uniform maximal inequality controls the complementary spatial tail.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The floor correction lies between zero and one time step. -/
theorem orientedHorizonShift_bounds {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ orientedHorizonShift n T ∧ orientedHorizonShift n T ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hf := Nat.floor_le (mul_nonneg hn'.le hT)
  have hc := Nat.lt_floor_add_one ((n : ℝ) * T)
  dsimp [orientedHorizonShift]
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hn').2
    nlinarith
  · apply (le_div_iff₀ hn').2
    have heq : ((⌊(n : ℝ) * T⌋₊ : ℝ) / n) * n = ⌊(n : ℝ) * T⌋₊ :=
      div_mul_cancel₀ _ (ne_of_gt hn')
    nlinarith

/-- Both the grid time and its shifted version lie in the continuum horizon. -/
theorem orientedHorizonShift_time_mem {n k : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 ≤ T)
    (hk : k ≤ ⌊(n : ℝ) * T⌋₊) :
    (k : ℝ) / n ∈ Set.Icc (0 : ℝ) T ∧
      (k : ℝ) / n + orientedHorizonShift n T ∈ Set.Icc (0 : ℝ) T := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ (⌊(n : ℝ) * T⌋₊ : ℝ) := by exact_mod_cast hk
  have hf := Nat.floor_le (mul_nonneg hn'.le hT)
  have hkT : (k : ℝ) / n ≤ T := by
    apply (div_le_iff₀ hn').2
    nlinarith
  have hshift := (orientedHorizonShift_bounds hn hT).1
  have hshiftT : (k : ℝ) / n + orientedHorizonShift n T ≤ T := by
    dsimp [orientedHorizonShift]
    have := (div_le_div_iff_of_pos_right hn').2 hk'
    linarith
  exact ⟨⟨by positivity, hkT⟩, ⟨add_nonneg (by positivity) hshift, hshiftT⟩⟩

/-- The floor correction changes the oriented stopping values by a quantity
    tending to zero for every bounded continuous reward. -/
theorem orientedStoppingSup_horizonShift_tendsto_zero {T M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (G : ℝ → ℝ → ℝ)
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2))
    (hGM : ∀ s y, |G s y| ≤ M) :
    Tendsto (fun n : ℕ =>
      orientedStoppingSup 2
          (fun k z => G ((k : ℝ) / n) (orientedScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0 -
      orientedStoppingSup 2
          (fun k z => G ((k : ℝ) / n + orientedHorizonShift n T) (orientedScaledSite n z))
          ⌊(n : ℝ) * T⌋₊ 0) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail : Tendsto (fun A : ℝ => 2 * M * ((T + 1) ^ 2 / (4 * A ^ 2))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun A : ℝ => (2 * M * (T + 1) ^ 2 / 4) / A ^ 2)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    convert hdiv using 1; funext A; ring
  have hevent : ∀ᶠ A : ℝ in atTop, 0 < A ∧
      2 * M * ((T + 1) ^ 2 / (4 * A ^ 2)) < ε / 2 :=
    (eventually_gt_atTop 0).and (htail.eventually (eventually_lt_nhds (by linarith)))
  obtain ⟨A, hA, hAtail⟩ := hevent.exists
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-A) A
  have huc : UniformContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) S :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hG.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (by linarith)
  have hmesh : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ := by
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
      simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    exact ht.eventually (eventually_lt_nhds hδ)
  refine eventually_atTop.mp ?_
  filter_upwards [hmesh, eventually_ge_atTop 1] with n hnmesh hn
  have hn0 : 0 < n := by omega
  let F : ℕ → Site 2 → ℝ := fun k z => G ((k : ℝ) / n) (orientedScaledSite n z)
  let F' : ℕ → Site 2 → ℝ := fun k z =>
    G ((k : ℝ) / n + orientedHorizonShift n T) (orientedScaledSite n z)
  have hlocal : ∀ p ∉ orientedScaledExit n T A, ∀ k ≤ ⌊(n : ℝ) * T⌋₊,
      |F k (orientedPath 0 p k) - F' k (orientedPath 0 p k)| ≤ ε / 2 := by
    intro p hp k hk
    let y := orientedScaledSite n (orientedPath 0 p k)
    have hy : |y| < A := by
      by_contra h
      exact hp ⟨k, hk, le_of_not_gt h⟩
    have htime := orientedHorizonShift_time_mem hn0 hT hk
    have hy' : y ∈ Set.Icc (-A) A := (abs_le.mp hy.le)
    have hdist : dist (((k : ℝ) / n, y) : ℝ × ℝ)
        (((k : ℝ) / n + orientedHorizonShift n T, y) : ℝ × ℝ) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      have hs := orientedHorizonShift_bounds hn0 hT
      have heq : (k : ℝ) / n - ((k : ℝ) / n + orientedHorizonShift n T) =
          -orientedHorizonShift n T := by ring
      rw [heq, abs_neg, abs_of_nonneg hs.1]
      exact lt_of_le_of_lt hs.2 hnmesh
    have hv := hmod _ ⟨htime.1, hy'⟩ _ ⟨htime.2, hy'⟩ hdist
    rw [Real.dist_eq] at hv
    exact hv.le
  have hv := abs_orientedStoppingSup_sub_le_of_local_reward (n := n) (T := T) (A := A)
    (by linarith : 0 ≤ ε / 2) F F' (fun k z => hGM _ _) (fun k z => hGM _ _) hlocal
  have hp := measureReal_orientedScaledExit_le hn hT hA
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * M by positivity)
  rw [Real.dist_eq, sub_zero]
  change |orientedStoppingSup 2 F ⌊(n : ℝ) * T⌋₊ 0 -
    orientedStoppingSup 2 F' ⌊(n : ℝ) * T⌋₊ 0| < ε
  linarith

end Parking
