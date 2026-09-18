/-
The discrepancy tail obtained from the logarithmic moment exponent.
-/
import Parking.Support.DiscrepancyRelative

noncomputable section
namespace Parking
open MeasureTheory Filter

/-- The discrepancy tail at every fixed positive fraction of the mean sandpile odometer. -/
theorem exists_discrepancy_tail {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((law d ν) {ω | ε * meanu (law d ν) n < |(U ω n 0 : ℝ) - uOf ω n 0|}).toReal ≤
        Real.exp (-(c * Real.log n ^ 2)) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  intro ε hε
  have hratio := eventually_discrepancy_relative_norm hd hd3 hGrowth hBern hConc hGN ν hν ε hε
  have ht := eventually_measure_gt_le_exp_log_sq (law d ν)
    (fun n ω => (U ω n 0 : ℝ) - uOf ω n 0) rHigh (fun n => ε * meanu (law d ν) n)
    (by norm_num : (0 : ℝ) < 1 / 16) rHigh_pos
    (fun n => integrable_diff_rpow hd ν hθ hexp (by linarith [two_le_rHigh n]) n) hratio
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  exact ⟨1 / 16, by norm_num, N, hN⟩
end Parking
