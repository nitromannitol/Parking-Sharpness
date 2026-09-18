/-
The logarithmic moment exponent and the critical U moment below dimension four.
-/
import Parking.Support.UpperTarget

noncomputable section
namespace Parking

/-- The logarithmic moment exponent has square root bounded by a quarter power. -/
theorem sqrt_rHigh_le_quarter {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (rHigh n) ≤ Real.sqrt (2 * rConst) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
  have hrc := rConst_pos
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 := rHigh_le_log hn
  have h2 := log_le_two_rpow_half n
  have hb : rHigh n ≤ 2 * rConst * (n : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith
  have hs := Real.sqrt_le_sqrt hb
  have heq : Real.sqrt ((n : ℝ) ^ ((1 : ℝ) / 2)) = (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
    norm_num
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * rConst), heq] at hs
  refine hs.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  exact Real.rpow_le_rpow hn0.le (by linarith) (by norm_num)

/-- At the logarithmic exponent the factor r*kappa is of order sqrt(r)*n^beta. -/
theorem rHigh_kappa_le_low {d n : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (hn : 2 ≤ n) :
    rHigh n * kappa d n ≤ 32 * Real.sqrt (2 * rConst) *
      Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  have hr0 := (rHigh_pos n).le
  have hsq : Real.sqrt (rHigh n) * kappa d n ≤
      32 * Real.sqrt (2 * rConst) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    calc Real.sqrt (rHigh n) * kappa d n
        ≤ (Real.sqrt (2 * rConst) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) * kappa d n :=
          mul_le_mul_of_nonneg_right (sqrt_rHigh_le_quarter hn) (kappa_nonneg d n)
      _ ≤ Real.sqrt (2 * rConst) * (32 * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) := by
        rw [mul_assoc, ← greenL2Rate_eq_low hd hd3 n]
        exact mul_le_mul_of_nonneg_left (kappa_term_le_greenL2Rate hd hd3 hn) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg (rHigh n))
  calc rHigh n * kappa d n = Real.sqrt (rHigh n) *
      (Real.sqrt (rHigh n) * kappa d n) := by rw [← mul_assoc, Real.mul_self_sqrt hr0]
    _ ≤ Real.sqrt (rHigh n) * (32 * Real.sqrt (2 * rConst) *
        (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) := hm
    _ = _ := by ring

theorem greenMaxRate_le_kappa {d n : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (hn : 2 ≤ n) :
    Parking.External.greenMaxRate d n ≤ kappa d n := by
  interval_cases d
  · simp [Parking.External.greenMaxRate, kappa]
  · simp only [Parking.External.greenMaxRate, kappa, show (2 : ℕ) ≠ 1 by decide,
      if_false, if_true]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
  · simp [Parking.External.greenMaxRate, kappa]
end Parking

namespace Parking
open MeasureTheory

/-- The logarithmic moment of U below dimension four. -/
theorem exists_U_rHigh_low {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      (∫ ω, (U ω n 0 : ℝ) ^ rHigh n ∂(law d ν)) ^ (1 / rHigh n)
        ≤ K * Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  haveI := hν.prob
  obtain ⟨C, hC, hcrit⟩ := exists_critical_moment hd hBern hConc ν hν
  obtain ⟨⟨_cL, CL, _hcL, hCL, hL⟩, ⟨_cM, CM, _hcM, hCM, hM⟩⟩ := hGN d hd
  obtain ⟨_b, B, _hb, hB, hBP⟩ := (hGrowth d hd (realLaw ν) (realLaw_isProbability ν)
    (realLaw_mean ν hν) (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν)
    (realLaw_expMoment ν hν)).1 hd3
  let Q := 32 * Real.sqrt (2 * rConst)
  have hQ : 0 < Q := by dsimp [Q]; have := rConst_pos; positivity
  refine ⟨C * (B + CL + (CM + Real.exp 2) * Q), by positivity, fun n hn => ?_⟩
  have hr0 := (rHigh_pos n).le
  have hs0 := Real.sqrt_nonneg (rHigh n)
  have hs1 : 1 ≤ Real.sqrt (rHigh n) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ rHigh n by linarith [two_le_rHigh n])
    simpa using h
  have hR0 : 0 ≤ (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hUk := (hcrit n (by omega) (rHigh n) (two_le_rHigh n)).2
  have hsp := (hBP n hn).2
  rw [← meanu_eq_meanSandpileReal hd ν n] at hsp
  have hl := (hL n hn).2
  rw [greenL2Rate_eq_low hd hd3 n] at hl
  have hm : greenMax d n ≤ CM * kappa d n := (hM n hn).2.trans
    (mul_le_mul_of_nonneg_left (greenMaxRate_le_kappa hd hd3 hn) hCM.le)
  have hk := rHigh_kappa_le_low hd hd3 hn
  change rHigh n * kappa d n ≤ Q * Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) at hk
  have he : ((n : ℝ) + 1) ^ (2 / rHigh n) ≤ Real.exp 2 :=
    rpow_two_div_le_exp_two (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      (rHigh_pos n) (log_le_rHigh n)
  have hterm1 : meanu (law d ν) n ≤ B * Real.sqrt (rHigh n) *
      (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    nlinarith [mul_nonneg (mul_nonneg hB.le (sub_nonneg.mpr hs1)) hR0]
  have hterm2 : Real.sqrt (rHigh n) * l2Norm (green d n) ≤
      CL * Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    nlinarith [mul_le_mul_of_nonneg_left hl hs0]
  have hterm3 : rHigh n * greenMax d n ≤ CM * Q * Real.sqrt (rHigh n) *
      (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    have h1 := mul_le_mul_of_nonneg_left hm hr0
    have h2 := mul_le_mul_of_nonneg_left hk hCM.le
    nlinarith
  have hterm4 : rHigh n * ((n : ℝ) + 1) ^ (2 / rHigh n) * kappa d n ≤
      Real.exp 2 * Q * Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    have h1 := mul_le_mul_of_nonneg_left he (mul_nonneg hr0 (kappa_nonneg d n))
    have h2 := mul_le_mul_of_nonneg_left hk (Real.exp_pos 2).le
    nlinarith
  have hinner : meanu (law d ν) n + Real.sqrt (rHigh n) * l2Norm (green d n) +
      rHigh n * greenMax d n + rHigh n * ((n : ℝ) + 1) ^ (2 / rHigh n) * kappa d n ≤
      (B + CL + (CM + Real.exp 2) * Q) * Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    nlinarith [hterm1, hterm2, hterm3, hterm4]
  exact hUk.trans (by nlinarith [mul_le_mul_of_nonneg_left hinner hC.le])
end Parking
