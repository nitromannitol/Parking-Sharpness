/- Cell representation and uniform approximation of the signed-density test coefficient. -/
import Parking.Support.SpatWWalkTaylor
import Parking.Support.SpatWSignedDecomp
import Parking.Support.NearestBallEvent
open Set Filter Topology LatticeProb MeasureTheory
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The scaled walk generator read on each cell of the rescaled lattice. -/
def scaledWalkTest (φ : (Fin d → ℝ) → ℝ) (R : ℝ) (x : Fin d → ℝ) : ℝ :=
  R ^ 2 * (walkOp (fun y => φ (fun j => (y j : ℝ) / R)) (latticePoint R x) -
    φ (fun j => ((latticePoint R x) j : ℝ) / R))

/-- Uniform approximation on entire lattice cells, including the floor-grid error. -/
theorem eventually_scaledWalkTest_error_le (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : IsTestFun φ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ x, |scaledWalkTest φ R x - contOp d φ x| ≤ ε := by
  have huc := (hasCompactSupport_contOp hφ).uniformContinuous_of_continuous (continuous_contOp hφ)
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (by positivity)
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_walkOp_taylor_error_le hd hφ (half_pos hε),
    eventually_gt_atTop (0 : ℝ), (tendsto_order.mp ht).2 δ hδ] with R hT hR hmesh x
  let z : Fin d → ℝ := fun i => ((latticePoint R x) i : ℝ) / R
  have hz : dist z x ≤ 1 / R := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    exact abs_floor_mul_div_sub_le hR (x i)
  have hC : |contOp d φ z - contOp d φ x| ≤ ε / 2 := (hm (hz.trans_lt hmesh)).le
  calc
    |scaledWalkTest φ R x - contOp d φ x|
        ≤ |scaledWalkTest φ R x - contOp d φ z| + |contOp d φ z - contOp d φ x| :=
      abs_sub_le _ _ _
    _ ≤ ε := by
      have hT' : |scaledWalkTest φ R x - contOp d φ z| ≤ ε / 2 := hT (latticePoint R x)
      linarith

/-- The floor-grid map recovers a lattice site at its rescaled position. -/
theorem latticePoint_rescale (y : Site d) {R : ℝ} (hR : R ≠ 0) :
    latticePoint R (fun i => (y i : ℝ) / R) = y := by
  funext i
  simp [latticePoint, mul_div_cancel₀ _ hR]

/-- At a lattice corner, the cell coefficient is the scaled walk generator. -/
theorem scaledWalkTest_rescale (φ : (Fin d → ℝ) → ℝ) (y : Site d) {R : ℝ}
    (hR : R ≠ 0) :
    scaledWalkTest φ R (fun i => (y i : ℝ) / R) =
      R ^ 2 * (walkOp (fun q => φ (fun i => (q i : ℝ) / R)) y -
        φ (fun i => (y i : ℝ) / R)) := by
  simp [scaledWalkTest, latticePoint_rescale y hR]

/-- The cell coefficient vanishes outside a fixed enlargement of the test support. -/
theorem scaledWalkTest_eq_zero_of_norm_gt {φ : (Fin d → ℝ) → ℝ} {B R : ℝ}
    (hbound : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R) {x : Fin d → ℝ}
    (hx : B + 2 < ‖x‖) : scaledWalkTest φ R x = 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hmesh : 1 / R ≤ 1 := (div_le_one hRpos).mpr hR
  let y := latticePoint R x
  let z : Fin d → ℝ := fun i => (y i : ℝ) / R
  have hz : ‖z - x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (abs_floor_mul_div_sub_le hRpos (x i)).trans hmesh
  have hfar : B + 1 < ‖z‖ := by
    have := norm_sub_le z (z - x)
    have heq : z - (z - x) = x := by abel
    rw [heq] at this
    linarith
  have hφz : φ z = 0 := by
    by_contra hne
    have := hbound z hne
    linarith
  have hpert : ∀ (i : Fin d) (t : ℝ), |t - z i| ≤ 1 → φ (Function.update z i t) = 0 := by
    intro i t ht
    by_contra hne
    have hb := hbound _ hne
    have hdist : ‖Function.update z i t - z‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases hji : j = i
      · subst j; simpa using ht
      · simp [Function.update_of_ne hji]
    have := norm_sub_le (Function.update z i t) (Function.update z i t - z)
    have heq : Function.update z i t - (Function.update z i t - z) = z := by abel
    rw [heq] at this
    linarith
  have hplus : ∀ i : Fin d, φ (fun j => ((y + unit i) j : ℝ) / R) = 0 := by
    intro i
    rw [Parking.Generic.LatticeTaylor.rescale_add_unit]
    apply hpert
    simpa [z, sub_sub, abs_of_pos hRpos] using hmesh
  have hminus : ∀ i : Fin d, φ (fun j => ((y - unit i) j : ℝ) / R) = 0 := by
    intro i
    rw [Parking.Generic.LatticeTaylor.rescale_sub_unit]
    apply hpert
    simpa [z, sub_sub, abs_of_pos hRpos] using hmesh
  have hwalk : walkOp (fun q => φ (fun i => (q i : ℝ) / R)) y = 0 := by
    simp only [walkOp, nbrSum, hplus, hminus, add_zero, Finset.sum_const_zero, zero_div]
  change R ^ 2 * (walkOp _ y - φ z) = 0
  rw [hwalk, hφz]
  ring

/-- Exact cell integration identifies the signed middle term with an odometer pairing. -/
theorem signedMiddle_eq_integral_scaledWalkTest {φ : (Fin d → ℝ) → ℝ}
    {B R : ℝ} (hB : 0 < B) (hbound : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R)
    (w : Data d) :
    signedMiddle w R φ = ∫ x, barOdometer w R 1 x * scaledWalkTest φ R x := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hRne := hRpos.ne'
  let f : (Fin d → ℝ) → ℝ := fun x => barOdometer w R 1 x * scaledWalkTest φ R x
  have hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ B + 2 := by
    intro x hx
    by_contra h
    have hz := scaledWalkTest_eq_zero_of_norm_gt hbound hR (lt_of_not_ge h)
    exact hx (by simp [f, hz])
  have hg : gridFn f R = f := by
    funext x
    simp only [gridFn, f, barOdometer, scaledWalkTest, latticePoint_rescale _ hRne]
    rfl
  have hi := integral_gridFn_eq_latticeSum (by linarith : 0 < B + 2) hf hR
  rw [hg] at hi
  change signedMiddle w R φ = ∫ x, f x
  rw [hi]
  have hterm : ∀ y : Site d, f (fun i => (y i : ℝ) / R) =
      (R ^ ((d : ℝ) / 2 - 2) * R ^ 2) * ((U w ⌊R ^ 2⌋₊ y : ℝ) *
        (walkOp (fun q => φ (fun i => (q i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R))) := by
    intro y
    dsimp [f]
    rw [scaledWalkTest_rescale _ _ hRne]
    simp only [barOdometer, one_mul, latticePoint_rescale _ hRne]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hpow : (1 / R) ^ d = R ^ (-(d : ℝ)) := by
    rw [one_div_pow, one_div, ← Real.rpow_natCast, Real.rpow_neg hRpos.le]
  have hfac : (R ^ ((d : ℝ) / 2 - 2) * R ^ 2) * (1 / R) ^ d = R ^ (-(d : ℝ) / 2) := by
    rw [hpow, ← Real.rpow_natCast, ← Real.rpow_add hRpos, ← Real.rpow_add hRpos]
    congr 1
    push_cast
    ring
  unfold signedMiddle
  rw [mul_assoc, mul_comm _ ((1 / R) ^ d), ← mul_assoc, hfac]
end Parking
