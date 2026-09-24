/-
The resampling coupling proof of the critical-density estimate. The coupled
marginals have the original law; persistent discrepancy labels satisfy the
physical count invariant, the fresh-pair hitting bound, and mass transport.
Their creation and cancellation expectations give the required quadratic
inequality for every resampling size.
-/
import Parking.Support.CancellationMean
import Parking.Support.CoupledMeans
import Parking.Support.LabelCreation

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- The resampling coupling bounds the loss of initial labels by the
opposite-pair hitting sum. -/
theorem Parking.coupling_bound_resample (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν = 0) (t : ℕ) :
    p.toReal * Parking.gammaOf ν - ((p.toReal * Parking.gammaOf ν) ^ 2 / 2) *
      (Parking.hitSum d (2 * t)).toReal ≤ 4 * Parking.S (Parking.law d ν) t := by
  have hint' := Parking.integrable_absDiff_prod ν hint
  have hsplit := Parking.discrepancy_initial_mean_split hd ν hp hint' t
  have hsurv : (∫⁻ ω : Parking.CoupledData d,
      (Parking.discrepancySurvivors ω.1.1 ω.1.2 ω.2 t 0 : ℝ≥0∞) ∂(Parking.coupledLaw d ν p)) ≤
      ENNReal.ofReal (4 * Parking.S (Parking.law d ν) t) := by
    rw [← Parking.lintegral_discrepancyAt_eq_survivors hd ν hp t]
    exact Parking.lintegral_discrepancyCount_le hd ν hp hint hmean t
  have hle : ENNReal.ofReal (p.toReal * Parking.gammaOf ν) ≤
      ENNReal.ofReal (4 * Parking.S (Parking.law d ν) t) +
        ENNReal.ofReal ((p.toReal * Parking.gammaOf ν) ^ 2 / 2) * Parking.hitSum d (2 * t) := by
    rw [hsplit]
    exact add_le_add hsurv (Parking.lintegral_discrepancyDead_le hd ν hp hint' t)
  have hγ : 0 ≤ Parking.gammaOf ν := integral_nonneg fun _ => abs_nonneg _
  have hε : 0 ≤ p.toReal * Parking.gammaOf ν := mul_nonneg ENNReal.toReal_nonneg hγ
  have hS : 0 ≤ 4 * Parking.S (Parking.law d ν) t := mul_nonneg (by norm_num) (Parking.S_nonneg _ t)
  have hC : 0 ≤ (p.toReal * Parking.gammaOf ν) ^ 2 / 2 := by positivity
  rw [← ENNReal.ofReal_toReal (Parking.hitSum_ne_top hd (2 * t)),
    ← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_add hS (mul_nonneg hC ENNReal.toReal_nonneg)] at hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal hε,
    ENNReal.toReal_ofReal (add_nonneg hS (mul_nonneg hC ENNReal.toReal_nonneg))] at hreal
  linarith

/-- **The coupling estimate of Steps 1--3.** It holds for every resampling
size between zero and the mean independent absolute difference. -/
theorem Parking.coupling_bound (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν = 0) :
    Parking.CouplingBound d ν := by
  intro t ε hε hεγ
  by_cases hγ : 0 < Parking.gammaOf ν
  · obtain ⟨hp, he⟩ := Parking.exists_resample_prob ν hγ hε hεγ
    have h := Parking.coupling_bound_resample hd ν hp hint hmean t
    rwa [he] at h
  · have he : ε = 0 := le_antisymm (le_trans hεγ (le_of_not_gt hγ)) hε
    rw [he]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Parking.S_nonneg _ t)

end
