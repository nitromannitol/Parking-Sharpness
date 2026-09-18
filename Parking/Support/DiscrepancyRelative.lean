/-
The relative discrepancy norm gains a positive power of time.
-/
import Parking.Support.DiscrepancyMoment
import Parking.Support.MomentTail

noncomputable section
namespace Parking
open MeasureTheory Filter

/-- A polynomial saving for the relative discrepancy moment norm. -/
theorem eventually_discrepancy_relative_norm {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      rNorm (law d ν) (rHigh n) (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) /
        (ε * meanu (law d ν) n) ≤ (n : ℝ) ^ (-((1 : ℝ) / 16)) ∧
        0 < ε * meanu (law d ν) n ∧ Real.log n ≤ rHigh n := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨C, hC, hMom⟩ := exists_discrepancy_moment hd hd3 hGrowth hBern hConc hGN ν hν
  obtain ⟨b, _B, hb, _hB, hBP⟩ := (hGrowth d hd (realLaw ν) (realLaw_isProbability ν)
    (realLaw_mean ν hν) (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν)
    (realLaw_expMoment ν hν)).1 hd3
  intro ε hε
  have hlog := eventually_log_succ_rpow_le (δ := (1 : ℝ) / 16) (γ := (5 : ℝ) / 4)
    hC (mul_pos hε hb) (by norm_num) (by norm_num)
  have hratio : ∀ᶠ n : ℕ in atTop,
      rNorm (law d ν) (rHigh n) (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) /
        (ε * meanu (law d ν) n) ≤ (n : ℝ) ^ (-((1 : ℝ) / 16)) ∧
        0 < ε * meanu (law d ν) n ∧ Real.log n ≤ rHigh n := by
    filter_upwards [eventually_ge_atTop 2, hlog] with n hn hL
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hsp := (hBP n hn).1
    rw [← meanu_eq_meanSandpileReal hd ν n] at hsp
    have hm : 0 < meanu (law d ν) n :=
      (mul_pos hb (Real.rpow_pos_of_pos hn0 _)).trans_le hsp
    have hεm := mul_pos hε hm
    refine ⟨?_, hεm, (Real.log_le_log hn0 (by linarith)).trans (log_le_rHigh n)⟩
    apply (div_le_iff₀ hεm).mpr
    have hrate := discrepancyRate_le_power hd hd3 hn
    have hrate0 : 0 ≤ (n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) := Real.rpow_nonneg hn0.le _
    have hpow : (n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 16) =
        (n : ℝ) ^ ((4 - (d : ℝ)) / 4) * (n : ℝ) ^ (-((1 : ℝ) / 16)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1; ring
    calc rNorm (law d ν) (rHigh n) (fun ω => (U ω n 0 : ℝ) - uOf ω n 0)
        ≤ C * discrepancyRate d n := (hMom n (by omega)).2
      _ ≤ C * ((n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) *
            Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hrate hC.le
      _ = (n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) *
          (C * Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4)) := by ring
      _ ≤ (n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) *
          ((ε * b) * (n : ℝ) ^ ((1 : ℝ) / 16)) := mul_le_mul_of_nonneg_left hL hrate0
      _ = (ε * (b * (n : ℝ) ^ ((4 - (d : ℝ)) / 4))) * (n : ℝ) ^ (-((1 : ℝ) / 16)) := by
        calc (n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) * ((ε * b) * (n : ℝ) ^ ((1 : ℝ) / 16))
            = (ε * b) * ((n : ℝ) ^ ((4 - (d : ℝ)) / 4 - (1 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 16)) := by ring
          _ = _ := by rw [hpow]; ring
      _ ≤ (ε * meanu (law d ν) n) * (n : ℝ) ^ (-((1 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsp hε.le) (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-((1 : ℝ) / 16)) * (ε * meanu (law d ν) n) := by ring
  exact hratio
end Parking
