/-
The second moment of the parking odometer at the critical density.

`eq:critical-moment` bounds the `r`-th moment root of `U_n(0)` for every
`r ≥ 2`; Steps 2 and 3 of `thm:upper` choose `r = 8` below dimension four and
`r = 2 ∨ ⌈log(n+1)⌉` above it, and the error terms are then at most a constant
multiple of `E u_n(0) + log n`.  Keeping the moment root instead of passing to
the mean by Jensen, as `Parking.exists_target` does, gives the bound the proof
of `prop:everyone-settles` quotes at `parking.tex:1511-1514`:
`(E U_n(0)^2)^{1/2} ≤ C (E u_n(0) + log n)`.
-/
import Parking.Support.UpperTarget
import Parking.Support.MomentLimits

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter

variable {d : ℕ}

theorem exists_rNorm_target (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration)
    (hGrowth : Parking.External.SandpileGrowth) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ r : ℝ, 2 ≤ r ∧
      Integrable (fun ω => ((U ω n 0 : ℕ) : ℝ) ^ r) (law d ν) ∧
      (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)
        ≤ C * (meanu (law d ν) n + Real.log n) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨C, hC, hCle⟩ := exists_critical_moment hd hBern hConc ν hν
  have hm0 : ∀ n : ℕ, (0 : ℝ) ≤ meanu (law d ν) n :=
    fun n => integral_nonneg fun ω => uOf_nonneg ω n 0
  by_cases hd3 : d ≤ 3
  · obtain ⟨K, hK, hKle⟩ := upper_error_low hd hd3 hGN
    obtain ⟨c, C', hc, hC', hBP⟩ :=
      (hGrowth d hd (realLaw ν) (realLaw_isProbability ν) (realLaw_mean ν hν)
        (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν)
        (realLaw_expMoment ν hν)).1 hd3
    refine ⟨C * (1 + K / c), by positivity, fun n hn => ⟨8, by norm_num, ?_, ?_⟩⟩
    · exact (hCle n (by omega) 8 (by norm_num)).1
    · have hbound := (hCle n (by omega) 8 (by norm_num)).2
      have herr := hKle n hn
      have hlow : c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ meanu (law d ν) n := by
        rw [meanu_eq_meanSandpileReal hd ν n]
        exact (hBP n hn).1
      have hlog0 : (0 : ℝ) ≤ Real.log n := le_of_lt (log_pos_of_two_le hn)
      have herr' : Real.sqrt 8 * l2Norm (green d n) + 8 * greenMax d n
          + 8 * (((n : ℝ) + 1) ^ ((2 : ℝ) / 8)) * kappa d n
            ≤ (K / c) * meanu (law d ν) n := by
        refine herr.trans ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]
        calc K * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) * c
            = K * (c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) := by ring
          _ ≤ K * meanu (law d ν) n := mul_le_mul_of_nonneg_left hlow hK.le
      have hKc0 : (0 : ℝ) ≤ K / c := le_of_lt (div_pos hK hc)
      calc (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (8 : ℝ) ∂(law d ν)) ^ (1 / (8 : ℝ))
          ≤ C * (meanu (law d ν) n + Real.sqrt 8 * l2Norm (green d n)
              + 8 * greenMax d n + 8 * ((n : ℝ) + 1) ^ (2 / (8 : ℝ)) * kappa d n) := hbound
        _ ≤ C * ((1 + K / c) * meanu (law d ν) n) := by
            refine mul_le_mul_of_nonneg_left ?_ hC.le
            have := herr'
            linarith
        _ ≤ C * (1 + K / c) * (meanu (law d ν) n + Real.log n) := by
            have h1 : (0 : ℝ) ≤ C * (1 + K / c) := by positivity
            nlinarith [mul_nonneg h1 hlog0]
  · have hd4 : 4 ≤ d := by omega
    obtain ⟨K, hK, hKle⟩ := upper_error_high hd4 hGN
    refine ⟨C * (1 + K), by positivity, fun n hn => ⟨rHigh n, two_le_rHigh n, ?_, ?_⟩⟩
    · exact (hCle n (by omega) (rHigh n) (two_le_rHigh n)).1
    · have hbound := (hCle n (by omega) (rHigh n) (two_le_rHigh n)).2
      have herr := hKle n hn
      have hlog0 : (0 : ℝ) ≤ Real.log n := le_of_lt (log_pos_of_two_le hn)
      calc (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (rHigh n) ∂(law d ν)) ^ (1 / rHigh n)
          ≤ C * (meanu (law d ν) n + Real.sqrt (rHigh n) * l2Norm (green d n)
              + rHigh n * greenMax d n
              + rHigh n * ((n : ℝ) + 1) ^ (2 / rHigh n) * kappa d n) := hbound
        _ ≤ C * (meanu (law d ν) n + K * Real.log n) := by
            refine mul_le_mul_of_nonneg_left ?_ hC.le
            linarith
        _ ≤ C * (1 + K) * (meanu (law d ν) n + Real.log n) := by
            have h1 : (0 : ℝ) ≤ C * Real.log n := mul_nonneg hC.le hlog0
            have h2 : (0 : ℝ) ≤ C * K * meanu (law d ν) n :=
              mul_nonneg (mul_nonneg hC.le hK.le) (hm0 n)
            nlinarith [h1, h2]


theorem exists_second_moment (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration)
    (hGrowth : Parking.External.SandpileGrowth) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Integrable (fun ω => ((U ω n 0 : ℕ) : ℝ) ^ 2) (law d ν) ∧
      ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ 2 ∂(law d ν)
        ≤ C * (meanu (law d ν) n + Real.log n) ^ 2 := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨C, hC, hCle⟩ := exists_rNorm_target hd hBern hConc hGrowth hGN ν hν
  obtain ⟨C₀, hC₀, hcrit⟩ := exists_critical_moment hd hBern hConc ν hν
  have hpow : ∀ (n : ℕ) (ω : Data d),
      ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℝ) = ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℕ) := by
    intro n ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨C ^ 2, by positivity, fun n hn => ?_⟩
  have hint2 : Integrable (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℝ)) (law d ν) :=
    (hcrit n (by omega) 2 (le_refl (2 : ℝ))).1
  have hint2' : Integrable (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℕ)) (law d ν) :=
    hint2.congr (Filter.Eventually.of_forall fun ω => hpow n ω)
  refine ⟨hint2', ?_⟩
  obtain ⟨r, hr2, hintr, hbound⟩ := hCle n hn
  have habs : ∀ ω : Data d, |((U ω n 0 : ℕ) : ℝ)| = ((U ω n 0 : ℕ) : ℝ) :=
    fun ω => abs_of_nonneg (Nat.cast_nonneg _)
  have hmeas : AEStronglyMeasurable (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ)) (law d ν) :=
    ((measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_U n 0)).aestronglyMeasurable
  have hmono := rNorm_mono_exponent (law d ν) (by norm_num : (1:ℝ) ≤ 2) hr2
    (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ)) hmeas
    (by simpa only [habs] using hint2) (by simpa only [habs] using hintr)
  have h2 : rNorm (law d ν) 2 (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ))
      = (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℝ) ∂(law d ν)) ^ (1 / (2 : ℝ)) := by
    simp only [rNorm, habs]
  have hr : rNorm (law d ν) r (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ))
      = (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r) := by
    simp only [rNorm, habs]
  rw [h2, hr] at hmono
  have hchain : (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℝ) ∂(law d ν)) ^ (1 / (2 : ℝ))
      ≤ C * (meanu (law d ν) n + Real.log n) := hmono.trans hbound
  have hI0 : (0 : ℝ) ≤ ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℝ) ∂(law d ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) 2
  have hsq := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hchain (by norm_num : (0:ℝ) ≤ 2)
  rw [← Real.rpow_mul hI0, one_div_mul_cancel (by norm_num : (2:ℝ) ≠ 0), Real.rpow_one] at hsq
  have hrhs : (C * (meanu (law d ν) n + Real.log n)) ^ (2 : ℝ)
      = C ^ 2 * (meanu (law d ν) n + Real.log n) ^ 2 := by
    have hb0 : (0 : ℝ) ≤ meanu (law d ν) n + Real.log n := by
      have h1 : (0 : ℝ) ≤ meanu (law d ν) n := integral_nonneg fun ω => uOf_nonneg ω n 0
      have h2 : (0 : ℝ) ≤ Real.log n := le_of_lt (log_pos_of_two_le hn)
      linarith
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hrhs] at hsq
  calc ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℕ) ∂(law d ν)
      = ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (2 : ℝ) ∂(law d ν) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (hpow n ω).symm
    _ ≤ C ^ 2 * (meanu (law d ν) n + Real.log n) ^ 2 := hsq

end Parking
