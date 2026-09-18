/- Replacement of the signed-density middle term by a continuum pairing. -/
import Parking.Support.SpatWTaylorRemainder
import Parking.Support.SpatWRiemann
import Parking.Support.ContOpRegularity
import Parking.Generic.VanishingMassError

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

/-- Taylor expansion and integration over lattice cells give an arbitrarily small
multiple of local odometer mass. -/
theorem eventually_signedMiddle_pairing_error_le (hd : 1 ≤ d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {B : ℝ} (hB : 0 < B)
    (hφB : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B)
    (hgB : ∀ x, contOp d φ x ≠ 0 → ‖x‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ w : Data d,
      |signedMiddle w R φ - ∫ x, barOdometer w R 1 x * contOp d φ x|
        ≤ ε * spatialLocalMass w R B := by
  obtain ⟨C, hC, hTaylor⟩ := exists_signedMiddle_taylor_bound hd hφ
  have hgc := continuous_contOp hφ
  have hgs := hasCompactSupport_contOp hφ
  have hgu : UniformContinuous (contOp d φ) :=
    hgc.uniformContinuous_of_tendsto_cocompact hgs.is_zero_at_infty
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.1 hgu (ε / 2) (by positivity)
  have hinv : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  have hcoef : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul C
  filter_upwards [eventually_ge_atTop (1 : ℝ), hinv.eventually (gt_mem_nhds hδ),
    hcoef.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))] with R hR hi hCR
  intro w
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let S := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)
  let T : ℝ := R ^ (-(d : ℝ) / 2 - 2) *
    ∑ y ∈ S, (U w ⌊R ^ 2⌋₊ y : ℝ) * contOp d φ (fun i => (y i : ℝ) / R)
  have hpow : R ^ (-(d : ℝ) / 2) / R ^ 2 = R ^ (-(d : ℝ) / 2 - 2) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_sub hRpos]
    norm_num
  have hmain : R ^ (-(d : ℝ) / 2) *
      ∑ y ∈ S, (U w ⌊R ^ 2⌋₊ y : ℝ) * (contOp d φ (fun i => (y i : ℝ) / R) / R ^ 2) = T := by
    simp only [T, ← mul_div_assoc, ← Finset.sum_div]
    rw [← hpow]
    ring
  have ht := hTaylor B hB hφB R hR w
  change |signedMiddle w R φ - _| ≤ _ at ht
  rw [hmain] at ht
  have herr : R ^ (-(d : ℝ) / 2) * (C / R ^ 3) *
      ∑ y ∈ S, (U w ⌊R ^ 2⌋₊ y : ℝ) = (C / R) * spatialLocalMass w R B := by
    unfold spatialLocalMass
    rw [← hpow]
    dsimp [S]
    field_simp
  rw [herr] at ht
  have hr := abs_barOdometer_riemann_error_le w hRpos
    (hgc.integrable_of_hasCompactSupport hgs) hgB
    (fun x z hxz => (show |contOp d φ x - contOp d φ z| < ε / 2 from
      by simpa [Real.dist_eq] using hmod ((hxz.trans_lt hi))).le)
  change |T - _| ≤ _ at hr
  have hmass := spatialLocalMass_nonneg w hRpos.le B
  calc |signedMiddle w R φ - ∫ x, barOdometer w R 1 x * contOp d φ x|
      ≤ |signedMiddle w R φ - T| + |T - ∫ x, barOdometer w R 1 x * contOp d φ x| :=
        abs_sub_le _ _ _
    _ ≤ C / R * spatialLocalMass w R B + ε / 2 * spatialLocalMass w R B := add_le_add ht hr
    _ ≤ ε * spatialLocalMass w R B := by nlinarith

/-- The Taylor and lattice-cell errors vanish in probability under the growth bound. -/
theorem tendsto_signedMiddle_sub_barOdometer_pairing_zero (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w |
      a < |signedMiddle w R φ - ∫ x, barOdometer w R 1 x * contOp d φ x|}).toReal)
      atTop (𝓝 0) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  obtain ⟨B₁, hB₁, hφB₁⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
  obtain ⟨B₂, hB₂, hgB₂⟩ := exists_norm_bound_of_hasCompactSupport (hasCompactSupport_contOp hφ)
  let B := max B₁ B₂
  have hB : 0 < B := hB₁.trans_le (le_max_left _ _)
  obtain ⟨C, hC, hbound⟩ := exists_integral_spatialLocalMass_le hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν hB
  exact Generic.VanishingMassError.tendsto_measure_gt_zero (law d ν) hC
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR using
      fun w => spatialLocalMass_nonneg w hR B)
    (Eventually.of_forall fun R => integrable_spatialLocalMass hd ν hν R B)
    (by filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR using hbound R hR)
    (fun ε hε => eventually_signedMiddle_pairing_error_le hd hφ hB
      (fun x hx => (hφB₁ x hx).trans (le_max_left _ _))
      (fun x hx => (hgB₂ x hx).trans (le_max_right _ _)) hε) ha

end Parking
end
