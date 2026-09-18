/-
The dimensional moment bounds for the difference of the two odometers.
-/
import Parking.Support.DiscrepancyNorm
import Parking.Support.DiscrepancyScale

noncomputable section
namespace Parking
open MeasureTheory

/-- The discrepancy moment bound, including every positive integer horizon. -/
theorem exists_discrepancy_moment {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => |(U ω n 0 : ℝ) - uOf ω n 0| ^ rHigh n) (law d ν) ∧
      rNorm (law d ν) (rHigh n) (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) ≤ C * discrepancyRate d n := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  obtain ⟨K, hK, hbound⟩ := exists_diff_rHigh_low hd hd3 hGrowth hBern hConc hGN ν hν
  let B := K * (Real.sqrt 2 + 4 ^ ((1 : ℝ) / 4))
  have hB : 0 < B := by dsimp [B]; positivity
  let X := rNorm (law d ν) (rHigh 1) (fun ω => (U ω 1 0 : ℝ) - uOf ω 1 0)
  let R := discrepancyRate d 1
  have hR : 0 < R := discrepancyRate_pos d (by norm_num)
  refine ⟨max B (X / R), hB.trans_le (le_max_left _ _), fun n hn => ⟨?_, ?_⟩⟩
  · exact integrable_diff_rpow hd ν hθ hexp (by linarith [two_le_rHigh n]) n
  · by_cases heq : n = 1
    · subst n
      exact (div_le_iff₀ hR).mp (le_max_right B (X / R))
    · have hn2 : 2 ≤ n := by omega
      have h1 := sqrt_kappa_log_le_discrepancyRate hd hd3 hn2
      have h2 := log_le_discrepancyRate d hn2
      have hinner : Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
          Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) + Real.log ((n : ℝ) + 1) ≤
            (Real.sqrt 2 + 4 ^ ((1 : ℝ) / 4)) * discrepancyRate d n := by
        nlinarith only [h1, h2]
      calc rNorm (law d ν) (rHigh n) (fun ω => (U ω n 0 : ℝ) - uOf ω n 0)
          ≤ K * (Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
            Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) + Real.log ((n : ℝ) + 1)) := hbound n hn2
        _ ≤ K * ((Real.sqrt 2 + 4 ^ ((1 : ℝ) / 4)) * discrepancyRate d n) :=
          mul_le_mul_of_nonneg_left hinner hK.le
        _ = B * discrepancyRate d n := by dsimp [B]; ring
        _ ≤ max B (X / R) * discrepancyRate d n :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (discrepancyRate_pos d hn).le
end Parking
