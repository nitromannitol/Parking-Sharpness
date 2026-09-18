/-
Approximation of the signed density by the scenery and the rescaled divisible-odometer pairing.
Taylor expansion, exact lattice-cell integration, the growth bound, and the vanishing distance
between odometers control the middle term. The martingale estimate supplies the final correction.
-/
import Parking.Support.SpatWMiddleApproximation
import Parking.Support.SpatWOdometerMass
import Parking.Generic.VanishingMass
import Parking.Support.SpatWPairingTransfer
import Parking.Support.SpatWMartingaleVariance
open Set Filter Topology MeasureTheory
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The Taylor and cell-integration error vanishes in probability by the local mass bound. -/
theorem tendsto_signedMiddle_sub_barOdometer_pairing_zero_of_walk_approximation
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w | a < |signedMiddle w R φ -
      ∫ x, barOdometer w R 1 x * contOp d φ x|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
  let K := Metric.closedBall (0 : Fin d → ℝ) (B + 2)
  obtain ⟨C, hC, hm⟩ := exists_integral_local_barOdometer_le hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν K (isCompact_closedBall _ _)
  apply Generic.VanishingMass.tendsto_measure_gt_zero
    (m := fun R w => ∫ x in K, barOdometer w R 1 x) (C := C) _ hC _ _ ha
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR w
    exact integral_nonneg (fun x => barOdometer_nonneg w hR 1 x)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    exact hm R hR
  · intro δ hδ
    exact eventually_abs_signedMiddle_sub_pairing_le hd hφ hB hbound hδ

/-- The signed middle term is asymptotic to the scale-dependent divisible-odometer pairing. -/
theorem tendsto_signedMiddle_sub_barDivisible_pairing_zero
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w | a < |signedMiddle w R φ -
      ∫ x, barDivisible w R 1 x * contOp d φ x|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  have h1 := fun a ha => tendsto_signedMiddle_sub_barOdometer_pairing_zero_of_walk_approximation hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν hφ (a := a) ha
  have h2 := fun a ha => tendsto_barOdometer_pairing_sub_barDivisible_pairing_zero hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν 1 zero_lt_one
    (continuous_contOp hφ) (hasCompactSupport_contOp hφ) (a := a) ha
  have h := Generic.VanishingMass.tendsto_measure_add_gt_zero h1 h2 ha
  simpa only [sub_add_sub_cancel] using h

/-- The signed density equals scenery plus the divisible-odometer pairing up to a vanishing error. -/
theorem tendsto_signedPair_sub_scenePair_sub_barDivisible_pairing_zero
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w | a < |signedPair w R φ - scenePair w R φ -
      ∫ x, barDivisible w R 1 x * contOp d φ x|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  have h1 := fun a ha => tendsto_signedMiddle_sub_barDivisible_pairing_zero hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν hφ (a := a) ha
  have h2 := tendsto_signedM_zero hd hd3 hGrowth hBernstein hConcentration hGreenNorms ν hν hφ
  have h := Generic.VanishingMass.tendsto_measure_add_gt_zero h1 h2 ha
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  congr 1
  apply measure_congr
  filter_upwards [ae_stack_nbr_law hd ν] with w hw
  have he := signedPair_eq_decomposition hw hφ hR
  have he' : signedMiddle w R φ - (∫ x, barDivisible w R 1 x * contOp d φ x) + signedM w R φ =
      signedPair w R φ - scenePair w R φ - ∫ x, barDivisible w R 1 x * contOp d φ x := by
    rw [he]
    ring
  exact congrArg (fun z : ℝ => a < |z|) he'
end Parking
