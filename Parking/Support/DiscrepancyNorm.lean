/-
The pathwise discrepancy estimate combined with the martingale moment bound.
-/
import Parking.Support.DiscrepancyRates

noncomputable section
namespace Parking
open MeasureTheory
variable {d : ℕ}

/-- The pathwise comparison read in the r-th moment norm. -/
theorem rNorm_diff_le_wStar (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ r : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν) (hr : 1 ≤ r) (n : ℕ) :
    rNorm (law d ν) r (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) ≤
      2 * (∫ ω, wStar ω n 0 ^ r ∂(law d ν)) ^ (1 / r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hIw : Integrable (fun ω : Data d => |2 * wStar ω n 0| ^ r) (law d ν) := by
    have h := (integrable_wStar_rpow hd ν hθ hexp hr n 0).const_mul (2 ^ r)
    have heq : ∀ ω : Data d, |2 * wStar ω n 0| ^ r = 2 ^ r * wStar ω n 0 ^ r := by
      intro ω
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (wStar_nonneg ω n 0)),
        Real.mul_rpow (by norm_num) (wStar_nonneg ω n 0)]
    simpa only [heq] using h
  have hmono : rNorm (law d ν) r (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) ≤
      rNorm (law d ν) r (fun ω => 2 * wStar ω n 0) := by
    refine rNorm_mono _ hr0 ?_ hIw
    refine (ae_stack_nbr_law hd ν).mono fun ω hω => ?_
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (wStar_nonneg ω n 0))]
    exact (pathwise_comparison_of_labelOrder hd hω n 0).2
  simpa only [rNorm_const_mul _ hr0 (by norm_num : (0 : ℝ) ≤ 2), rNorm_wStar] using hmono

/-- The discrepancy moment bounded by the martingale moment. -/
theorem exists_rNorm_diff_bound (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      rNorm (law d ν) r (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) ≤
        C * ((n : ℝ) + 1) ^ (1 / r) *
          (Real.sqrt (r * kappa d n *
            (∫ ω, (U ω n 0 : ℝ) ^ r ∂(law d ν)) ^ (1 / r)) + r) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  obtain ⟨C, hC, hbound⟩ := exists_wErr_moment_const hd hBern ν hθ hexp
  refine ⟨2 * C, by positivity, fun n hn r hr => ?_⟩
  have hr1 : 1 ≤ r := by linarith
  have hS := wStar_moment_bound hd ν hθ hexp hr1 n
  have hM := hbound n hn r hr
  have hD := rNorm_diff_le_wStar hd ν hθ hexp hr1 n
  have hfactor : 0 ≤ ((n : ℝ) + 1) ^ (1 / r) := Real.rpow_nonneg (by positivity) _
  have h := mul_le_mul_of_nonneg_left hM hfactor
  nlinarith

/-- Taking a square root of r times sqrt(r) gives r^(3/4). -/
theorem sqrt_r_mul_sqrt {r K k R : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    Real.sqrt (r * k * (K * Real.sqrt r * R)) =
      Real.sqrt K * r ^ ((3 : ℝ) / 4) * Real.sqrt (k * R) := by
  have hp : Real.sqrt (r * Real.sqrt r) = r ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_mul hr.le]
    simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    rw [← Real.rpow_add hr]
    norm_num
  rw [show r * k * (K * Real.sqrt r * R) = K * (r * Real.sqrt r) * (k * R) by ring,
    Real.sqrt_mul (mul_nonneg hK (mul_nonneg hr.le (Real.sqrt_nonneg r))),
    Real.sqrt_mul hK, hp]
end Parking

namespace Parking
open MeasureTheory

/-- The remaining logarithmic factor in the low-dimensional discrepancy bound. -/
theorem exists_diff_rHigh_low {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      rNorm (law d ν) (rHigh n) (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) ≤
        K * (Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
          Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) + Real.log ((n : ℝ) + 1)) := by
  obtain ⟨C, hC, hdiff⟩ := exists_rNorm_diff_bound hd hBern ν hν
  obtain ⟨K, hK, hU⟩ := exists_U_rHigh_low hd hd3 hGrowth hBern hConc hGN ν hν
  let B := Real.sqrt K * rConst ^ ((3 : ℝ) / 4)
  have hrc := rConst_pos
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C * Real.exp 2 * (B + rConst), by positivity, fun n hn => ?_⟩
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hr0 := rHigh_pos n
  have hrL : rHigh n ≤ rConst * Real.log ((n : ℝ) + 1) := (rHigh_le_log hn).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log hn0 (by linarith)) hrc.le)
  have hrq : (rHigh n) ^ ((3 : ℝ) / 4) ≤
      rConst ^ ((3 : ℝ) / 4) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
    rw [← Real.mul_rpow hrc.le hL0.le]
    exact Real.rpow_le_rpow hr0.le hrL (by norm_num)
  have hX := hU n hn
  have hs : Real.sqrt (rHigh n * kappa d n *
      (∫ ω, (U ω n 0 : ℝ) ^ rHigh n ∂(law d ν)) ^ (1 / rHigh n)) ≤
      B * (Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
        Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)) := by
    calc Real.sqrt (rHigh n * kappa d n *
        (∫ ω, (U ω n 0 : ℝ) ^ rHigh n ∂(law d ν)) ^ (1 / rHigh n))
        ≤ Real.sqrt (rHigh n * kappa d n *
          (K * Real.sqrt (rHigh n) * (n : ℝ) ^ ((4 - (d : ℝ)) / 4))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hX (mul_nonneg hr0.le (kappa_nonneg d n)))
      _ = Real.sqrt K * (rHigh n) ^ ((3 : ℝ) / 4) *
          Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) :=
            sqrt_r_mul_sqrt hr0 hK.le
      _ ≤ Real.sqrt K * (rConst ^ ((3 : ℝ) / 4) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)) *
          Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrq (Real.sqrt_nonneg K)) (Real.sqrt_nonneg _)
      _ = _ := by dsimp [B]; ring
  have he : ((n : ℝ) + 1) ^ (1 / rHigh n) ≤ Real.exp 2 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ (n : ℝ) + 1)
      (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hr0.le)).trans ?_
    exact rpow_two_div_le_exp_two (by linarith) hr0 (log_le_rHigh n)
  have hD := hdiff n (by omega) (rHigh n) (two_le_rHigh n)
  have hA0 : 0 ≤ Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
      Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL0.le _)
  have hS0 : 0 ≤ Real.sqrt (rHigh n * kappa d n *
      (∫ ω, (U ω n 0 : ℝ) ^ rHigh n ∂(law d ν)) ^ (1 / rHigh n)) + rHigh n := by positivity
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) hS0
  have h2 : Real.sqrt (rHigh n * kappa d n *
      (∫ ω, (U ω n 0 : ℝ) ^ rHigh n ∂(law d ν)) ^ (1 / rHigh n)) + rHigh n ≤
      (B + rConst) * (Real.sqrt (kappa d n * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) *
          Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) + Real.log ((n : ℝ) + 1)) := by
    nlinarith [mul_nonneg hB.le hL0.le, mul_nonneg hrc.le hA0]
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC.le (Real.exp_pos 2).le)
  nlinarith
end Parking
