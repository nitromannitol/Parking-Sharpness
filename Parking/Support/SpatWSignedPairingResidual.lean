/- The signed-density residual relative to the divisible odometer pairing. -/
import Parking.Support.SpatWMiddlePairingError
import Parking.Support.SpatWPairingTransfer

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

/-- The signed density equals the scenery plus the current-scale divisible pairing,
up to an error vanishing in probability. -/
theorem tendsto_signedPair_sub_scenePair_sub_pairing_zero {d : ℕ}
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w | a < |signedPair w R φ - scenePair w R φ
      - ∫ x, barDivisible w R 1 x * contOp d φ x|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  let E₁ := fun R (w : Data d) => signedMiddle w R φ -
    ∫ x, barOdometer w R 1 x * contOp d φ x
  let E₂ := fun R (w : Data d) => (∫ x, barOdometer w R 1 x * contOp d φ x) -
    ∫ x, barDivisible w R 1 x * contOp d φ x
  have h₁ : ∀ b : ℝ, 0 < b →
      Tendsto (fun R => ((law d ν) {w | b < |E₁ R w|}).toReal) atTop (𝓝 0) :=
    fun _ hb => tendsto_signedMiddle_sub_barOdometer_pairing_zero hd hd3
      hGrowth hBernstein hConcentration hGreenNorms ν hν hφ hb
  have h₂ : ∀ b : ℝ, 0 < b →
      Tendsto (fun R => ((law d ν) {w | b < |E₂ R w|}).toReal) atTop (𝓝 0) :=
    fun _ hb => tendsto_barOdometer_sub_barDivisible_pairing_zero hd hd3
      hGrowth hBernstein hConcentration hGreenNorms ν hν
      (continuous_contOp hφ) (hasCompactSupport_contOp hφ) hb
  have hsum := Generic.VanishingMassError.tendsto_measure_add_gt_zero (law d ν)
    (fun b hb => Generic.VanishingMassError.tendsto_measure_add_gt_zero (law d ν) h₁ h₂ hb)
    (tendsto_signedM_zero hd hd3 hGrowth hBernstein hConcentration hGreenNorms ν hν hφ) ha
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  congr 1
  apply measure_congr
  filter_upwards [ae_stack_nbr_law hd ν] with w hw
  have he : E₁ R w + E₂ R w + signedM w R φ = signedPair w R φ - scenePair w R φ
      - ∫ x, barDivisible w R 1 x * contOp d φ x := by
    rw [signedPair_eq_decomposition hw hφ hR]
    dsimp [E₁, E₂]
    ring
  exact congrArg (fun z : ℝ => a < |z|) he

end Parking
end
