/-
Bounded ratios for fixed dimension-four laws and no bound uniform over laws.
-/
import Parking.Support.MeanPos
import Parking.Support.GrowthMeans
import Parking.Frozen.FourSparse

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped Topology

/-- In dimension four, each fixed critical law has a bounded ratio at every positive horizon. -/
theorem four_mean_ratio_bounds (hGrowth : Parking.External.SandpileGrowth)
    (hBern : Parking.External.Bernstein) (hConc : Parking.External.UConcentration)
    (hGN : Parking.External.GreenNorms) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ meanU (law 4 ν) n / meanu (law 4 ν) n) ∧
    ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n → meanU (law 4 ν) n / meanu (law 4 ν) n ≤ B := by
  haveI := hν.prob
  constructor
  · intro n hn
    apply (le_div_iff₀ (meanu_pos (by norm_num) ν hν n hn)).mpr
    simpa only [one_mul] using meanu_le_meanU (by norm_num) ν hν.integrable_abs n
  · obtain ⟨c, C, _hc, hC, hU⟩ := (meanU_growth hGrowth hBern hConc hGN 4
      (by norm_num) ν hν).2 (by norm_num)
    have hBP := hGrowth 4 (by norm_num) (realLaw ν) inferInstance (realLaw_mean ν hν)
      (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν) (realLaw_expMoment ν hν)
    obtain ⟨a, A, ha, _hA, hu⟩ := hBP.2.1 rfl
    refine ⟨max 1 (C / a), fun n hn => ?_⟩
    by_cases hn1 : n = 1
    · subst n
      rw [meanU_one_eq_S_zero (by norm_num) ν hν.integrable_abs,
        ← meanu_one_eq_S_zero ν, div_self (meanu_pos (by norm_num) ν hν 1 (by norm_num)).ne']
      exact le_max_left _ _
    · have hn2 : 2 ≤ n := by omega
      apply le_trans (b := C / a) ?_ (le_max_right _ _)
      apply (div_le_iff₀ (meanu_pos (by norm_num) ν hν n hn)).mpr
      have hl := (hu n hn2).1
      rw [← meanu_eq_meanSandpileReal (by norm_num) ν n] at hl
      calc meanU (law 4 ν) n ≤ C * Real.log n := (hU n hn2).2
        _ = C / a * (a * Real.log n) := by field_simp
        _ ≤ C / a * meanu (law 4 ν) n := mul_le_mul_of_nonneg_left hl (by positivity)

/-- The dimension-four ratio has no bound uniform over the critical initial law. -/
theorem exists_four_mean_ratio_large (hGrowth : Parking.External.SandpileGrowth)
    (hBern : Parking.External.Bernstein) (hConc : Parking.External.UConcentration)
    (hGN : Parking.External.GreenNorms) (hStopping : Parking.External.Stopping)
    (B : ℝ) (_hB : 0 < B) :
    ∃ ν : Measure ℤ, CriticalLaw ν ∧
      B ≤ liminf (fun n : ℕ => meanU (law 4 ν) n / meanu (law 4 ν) n) atTop := by
  obtain ⟨c, hc, hs⟩ := Parking.Frozen.four_sparse hGrowth hStopping
  let M : ℝ := max (B / c) (Real.log 2)
  let ε : ℝ := Real.exp (-M)
  have hε : 0 < ε := Real.exp_pos _
  have hε2 : ε ≤ 1 / 2 := by
    have h := Real.exp_le_exp.mpr (neg_le_neg (le_max_right (B / c) (Real.log 2)))
    simpa only [ε, M, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have hν : CriticalLaw (threePointLaw (ε / 2)) :=
    criticalLaw_threePointLaw (by positivity) (by linarith)
  refine ⟨threePointLaw (ε / 2), hν, ?_⟩
  have hL : Real.log (Real.exp 1 / ε) = 1 + M := by
    rw [Real.log_div (Real.exp_ne_zero 1) hε.ne', show Real.log ε = -M from Real.log_exp _,
      Real.log_exp]
    ring
  have hBc : B ≤ c * Real.log (Real.exp 1 / ε) := by
    rw [hL]
    have hM : B / c ≤ M := le_max_left _ _
    rw [div_le_iff₀ hc] at hM
    nlinarith only [hM, hc]
  obtain ⟨K, hK⟩ := (four_mean_ratio_bounds hGrowth hBern hConc hGN _ hν).2
  have hb : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun n : ℕ => meanU (law 4 (threePointLaw (ε / 2))) n /
        meanu (law 4 (threePointLaw (ε / 2))) n) :=
    ⟨K, eventually_atTop.mpr ⟨1, hK⟩⟩
  exact le_liminf_of_le hb.isCoboundedUnder_ge ((hs ε hε hε2).mono fun _ h => hBc.trans h)
end Parking
