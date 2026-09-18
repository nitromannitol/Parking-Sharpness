/-
The growth of the mean particle odometer, obtained by inserting the mean
sandpile estimates into the master comparison.
-/
import Parking.Frozen.Master

noncomputable section
namespace Parking
open MeasureTheory

/-- The two mean growth regimes in the critical law. -/
theorem meanU_growth (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ meanU (law d ν) n ∧
        meanU (law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (law d ν) n ∧
        meanU (law d ν) n ≤ C * Real.log n) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  obtain ⟨a, A, ha, haA, hM⟩ := Parking.Frozen.master hGrowth hBernstein
    hConcentration hGreenNorms d hd ν hν.prob hν.nonconst hν.mean θ hθ hexp
  have hA : 0 < A := ha.trans_le haA
  have hBP := hGrowth d hd (realLaw ν) (realLaw_isProbability ν) (realLaw_mean ν hν)
    (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν) (realLaw_expMoment ν hν)
  constructor
  · intro hd3
    obtain ⟨b, B, hb, hB, hbound⟩ := hBP.1 hd3
    let β : ℝ := (4 - (d : ℝ)) / 4
    have hβ : 0 < β := by
      have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
      dsimp [β]; linarith
    refine ⟨a * b, A * (B + 1 / β), mul_pos ha hb, by positivity, fun n hn => ?_⟩
    have hsp := hbound n hn
    rw [← meanu_eq_meanSandpileReal hd ν n] at hsp
    have hlog0 : 0 ≤ Real.log n := (log_pos_of_two_le hn).le
    have hlog : Real.log n ≤ (1 / β) * (n : ℝ) ^ β := by
      simpa only [one_div, inv_mul_eq_div] using
        Real.log_le_rpow_div (Nat.cast_nonneg n) hβ
    obtain ⟨hMl, hMu⟩ := hM n hn
    constructor
    · calc a * b * (n : ℝ) ^ β = a * (b * (n : ℝ) ^ β) := by ring
        _ ≤ a * (meanu (law d ν) n + Real.log n) :=
          mul_le_mul_of_nonneg_left (by linarith [hsp.1]) ha.le
        _ ≤ meanU (law d ν) n := hMl
    · calc meanU (law d ν) n ≤ A * (meanu (law d ν) n + Real.log n) := hMu
        _ ≤ A * (B * (n : ℝ) ^ β + (1 / β) * (n : ℝ) ^ β) :=
          mul_le_mul_of_nonneg_left (add_le_add hsp.2 hlog) hA.le
        _ = A * (B + 1 / β) * (n : ℝ) ^ β := by ring
  · intro hd4
    have hsp : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
        meanu (law d ν) n ≤ B * Real.log n := by
      by_cases heq : d = 4
      · obtain ⟨b, B, _hb, hB, hbound⟩ := hBP.2.1 heq
        exact ⟨B, hB, fun n hn => by
          rw [meanu_eq_meanSandpileReal hd ν n]; exact (hbound n hn).2⟩
      · obtain ⟨b, B, _hb, hB, hbound⟩ := hBP.2.2.1 (by omega)
        refine ⟨2 * B, by positivity, fun n hn => ?_⟩
        rw [meanu_eq_meanSandpileReal hd ν n]
        calc Parking.External.meanSandpileReal d (realLaw ν) n
            ≤ B * Real.log ((n : ℝ) + 1) := (hbound n hn).2
          _ ≤ B * (2 * Real.log n) :=
            mul_le_mul_of_nonneg_left (log_succ_le_two_mul_log hn) hB.le
          _ = 2 * B * Real.log n := by ring
    obtain ⟨B, hB, hsp⟩ := hsp
    refine ⟨a, A * (B + 1), ha, by positivity, fun n hn => ?_⟩
    have hsp0 : 0 ≤ meanu (law d ν) n := integral_nonneg fun ω => uOf_nonneg ω n 0
    obtain ⟨hMl, hMu⟩ := hM n hn
    constructor
    · exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hsp0) ha.le).trans hMl
    · calc meanU (law d ν) n ≤ A * (meanu (law d ν) n + Real.log n) := hMu
        _ ≤ A * (B * Real.log n + Real.log n) :=
          mul_le_mul_of_nonneg_left (by linarith [hsp n hn]) hA.le
        _ = A * (B + 1) * Real.log n := by ring
end Parking
