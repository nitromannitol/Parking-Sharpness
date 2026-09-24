import Parking.Support.SingleHoleWeight
import Parking.Support.SingleHoleTerminal
import Parking.Support.LayerSubmartingale

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Adding one particle reduces a site's expected hole count by at most its hitting probability. -/
theorem matchedMeanH_addParticle_relative (hd : 3 ≤ d) (η : Site d → ℤ) (v x : Site d)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) :
    escapePotential d x v * matchedMeanH η ρ T x ≤ matchedMeanH (addParticle v η) ρ T x ∧
      matchedMeanH (addParticle v η) ρ T x ≤ matchedMeanH η ρ T x := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  haveI := roundNoiseLaw_isProbability hd1
  have hwm (s : ℕ) := measurable_singleHoleWeight hd η v ρ T s x
  have hwb (σ : RoundNoise d) (s : ℕ) : ‖singleHoleWeight η v ρ σ T s x‖ ≤ ((-η x).toNat : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (singleHoleWeight_bounds hd η v ρ σ T s x).1]
    exact (singleHoleWeight_bounds hd η v ρ σ T s x).2
  have hstep := layer_submartingale_integral_le (Measure.infinitePi fun _ : RoundSlot d => stepLaw d)
    (fun σ s => singleHoleWeight η v ρ σ T s x) hwm _ hwb T
    (fun s hs σ => singleHoleWeight_section_ge hd η v ρ σ T s hs x)
  have hzero (σ : RoundNoise d) : singleHoleWeight η v ρ σ T 0 x = matchedMeanH η ρ T x * escapePotential d x v := by
    rw [singleHoleWeight, futureHoleValue_zero]
    rfl
  have ht := integral_mono (Integrable.of_bound (hwm T).aestronglyMeasurable _ (ae_of_all _ fun σ => hwb σ T))
    (integrable_matchedHoles hd1 (addParticle v η) ρ T x (roundNoiseLaw d))
    (fun σ => by
      change singleHoleWeight η v ρ σ T T x ≤ _
      rw [singleHoleWeight, futureHoleValue_terminal hd1]
      exact singleAddition_hole_escape_terminal hd η v x ρ σ T)
  constructor
  · have h := hstep.trans ht
    simp only [hzero, integral_const, probReal_univ, one_smul] at h
    simpa only [matchedMeanH, mul_comm] using h
  · exact integral_mono (integrable_matchedHoles hd1 (addParticle v η) ρ T x (roundNoiseLaw d))
      (integrable_matchedHoles hd1 η ρ T x (roundNoiseLaw d))
      (fun σ => Nat.cast_le.mpr (singleAddition_counts_mono η v ρ σ T x).2)
end Parking
