/- Cellwise consistency of the space-time test coefficients. -/
import Parking.Support.SpatialSpaceTimeTaylor
import Parking.Support.SpatialRescaledEquation
import Parking.Generic.TimeTestApproximation

open Set Filter Topology LatticeProb
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The left temporal endpoint of the cell containing a nonnegative time. -/
def parabolicTime (R s : ℝ) : ℝ := (⌊s * R ^ 2⌋₊ : ℝ) / R ^ 2

/-- The forward time difference, constant on each parabolic cell. -/
def parabolicTimeTest (ψ : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ)
    (p : ℝ × (Fin d → ℝ)) : ℝ :=
  R ^ 2 * (ψ (parabolicTime R p.1 + 1 / R ^ 2,
    fun i => ((latticePoint R p.2) i : ℝ) / R) -
    ψ (parabolicTime R p.1, fun i => ((latticePoint R p.2) i : ℝ) / R))

/-- The spatial generator tested at the next temporal endpoint. -/
def parabolicSpaceTest (ψ : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ)
    (p : ℝ × (Fin d → ℝ)) : ℝ :=
  scaledWalkTest (fun x => ψ (parabolicTime R p.1 + 1 / R ^ 2, x)) R p.2

theorem abs_parabolicTime_sub_le {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) :
    |parabolicTime R s - s| ≤ 1 / R ^ 2 := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hl := Nat.floor_le (mul_nonneg hs hR2.le)
  have hu := Nat.lt_floor_add_one (s * R ^ 2)
  rw [parabolicTime, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hR2).mpr hl))]
  apply (le_div_iff₀ hR2).mpr
  have he : (s - (⌊s * R ^ 2⌋₊ : ℝ) / R ^ 2) * R ^ 2 =
      s * R ^ 2 - (⌊s * R ^ 2⌋₊ : ℝ) := by field_simp
  rw [he]
  linarith

theorem dist_parabolicGrid_le {R : ℝ} (hR : 0 < R)
    (p : ℝ × (Fin d → ℝ)) (hp : 0 ≤ p.1) :
    dist (parabolicTime R p.1, fun i => ((latticePoint R p.2) i : ℝ) / R) p ≤
      max (1 / R ^ 2) (1 / R) := by
  rw [Prod.dist_eq]
  apply max_le_max
  · exact abs_parabolicTime_sub_le hR hp
  · apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    exact abs_floor_mul_div_sub_le hR (p.2 i)

/-- The forward coefficient converges uniformly on all nonnegative times and all space. -/
theorem eventually_parabolicTimeTest_error_le
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ p : ℝ × (Fin d → ℝ), 0 ≤ p.1 →
      |parabolicTimeTest ψ R p - deriv (fun s => ψ (s, p.2)) p.1| ≤ ε := by
  obtain ⟨δ, hδ, hm⟩ := Generic.TimeTest.exists_forward_difference_modulus hψ.1 hψ.2.1
    (half_pos hε)
  have huc := (Generic.TimeTest.hasCompactSupport_timeDeriv
    (hψ.1.differentiable (by simp)) hψ.2.1).uniformContinuous_of_continuous
    (Generic.TimeTest.contDiff_timeDeriv hψ.1).continuous
  obtain ⟨ρ, hρ, hc⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ht2 : Tendsto (fun R : ℝ => 1 / R ^ 2) atTop (𝓝 0) := by
    simpa only [one_div_pow, zero_pow (by norm_num : 2 ≠ 0)] using ht.pow 2
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_order.mp ht2).2 δ hδ,
    (tendsto_order.mp ht2).2 ρ hρ, (tendsto_order.mp ht).2 ρ hρ] with R hR hmesh htime hspace p hp
  let q : ℝ × (Fin d → ℝ) :=
    (parabolicTime R p.1, fun i => ((latticePoint R p.2) i : ℝ) / R)
  have hdq : dist q p < ρ := (dist_parabolicGrid_le hR p hp).trans_lt (max_lt htime hspace)
  have hdiff := (hm (1 / R ^ 2) (by positivity) hmesh q.1 q.2).le
  have hcont := (hc hdq).le
  rw [Real.dist_eq] at hcont
  simp only [Prod.mk.eta] at hdiff
  have he : (ψ (q.1 + 1 / R ^ 2, q.2) - ψ q) / (1 / R ^ 2) =
      parabolicTimeTest ψ R p := by simp [parabolicTimeTest, q, mul_comm]
  rw [he] at hdiff
  exact (abs_sub_le (parabolicTimeTest ψ R p) (Generic.TimeTest.timeDeriv ψ q)
    (Generic.TimeTest.timeDeriv ψ p)).trans (by linarith)

/-- The spatial coefficient converges uniformly, including the time and floor-grid shifts. -/
theorem eventually_parabolicSpaceTest_error_le (hd : 1 ≤ d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ p : ℝ × (Fin d → ℝ), 0 ≤ p.1 →
      |parabolicSpaceTest ψ R p - contOp d (fun x => ψ (p.1, x)) p.2| ≤ ε := by
  have huc := (hasCompactSupport_spaceTime_contOp hψ).uniformContinuous_of_continuous
    (contDiff_spaceTime_contOp hψ.1).continuous
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ht2 : Tendsto (fun R : ℝ => 1 / R ^ 2) atTop (𝓝 0) := by
    simpa only [one_div_pow, zero_pow (by norm_num : 2 ≠ 0)] using ht.pow 2
  filter_upwards [eventually_spaceTime_walkOp_taylor_error_le hd hψ (half_pos hε),
    eventually_gt_atTop (0 : ℝ), (tendsto_order.mp ht2).2 (δ / 2) (half_pos hδ),
    (tendsto_order.mp ht).2 δ hδ] with R hT hR htime hspace p hp
  let q : ℝ × (Fin d → ℝ) :=
    (parabolicTime R p.1 + 1 / R ^ 2, fun i => ((latticePoint R p.2) i : ℝ) / R)
  have hdist : dist q p < δ := by
    rw [Prod.dist_eq]
    apply max_lt
    · have he : |q.1 - p.1| ≤ |parabolicTime R p.1 - p.1| + 1 / R ^ 2 := by
        have := abs_add_le (parabolicTime R p.1 - p.1) (1 / R ^ 2)
        simpa [q, sub_add_eq_add_sub, abs_of_pos (by positivity : 0 < 1 / R ^ 2)] using this
      rw [Real.dist_eq]
      linarith [abs_parabolicTime_sub_le hR hp]
    · apply lt_of_le_of_lt _ hspace
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      exact abs_floor_mul_div_sub_le hR (p.2 i)
  have hcont := (hm hdist).le
  rw [Real.dist_eq] at hcont
  have hTaylor := hT q.1 (latticePoint R p.2)
  change |parabolicSpaceTest ψ R p - contOp d (fun x => ψ (q.1, x)) q.2| ≤ ε / 2 at hTaylor
  exact (abs_sub_le (parabolicSpaceTest ψ R p) (contOp d (fun x => ψ (q.1, x)) q.2)
    (contOp d (fun x => ψ (p.1, x)) p.2)).trans (by linarith)

end Parking
