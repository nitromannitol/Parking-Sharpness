/-
The sparse dimension-four ratio from the critical lower bound and convex comparison.
-/
import Parking.Support.SparseCompare
import Parking.Support.DensitySequence
import Parking.Frozen.CorCritical

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped Topology

/-- Divide a uniform logarithmic lower bound by a logarithmic upper bound. -/
theorem eventually_ratio_ge_log_scale (f g : ℕ → ℝ) {a C D L : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hL : 0 < L)
    (hf : ∀ n : ℕ, 2 ≤ n → 0 < f n)
    (hu : ∀ n : ℕ, 2 ≤ n → f n ≤ C * Real.log n / L)
    (hl : ∀ n : ℕ, 2 ≤ n → a * Real.log n - D ≤ g n) :
    ∀ᶠ n : ℕ in atTop, a / (2 * C) * L ≤ g n / f n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 * D / a)), eventually_ge_atTop 2]
    with n hn hn2
  have hD : D ≤ a / 2 * Real.log n := by
    rw [div_le_iff₀ ha] at hn
    linarith
  apply (le_div_iff₀ (hf n hn2)).mpr
  calc a / (2 * C) * L * f n ≤ a / (2 * C) * L * (C * Real.log n / L) :=
      mul_le_mul_of_nonneg_left (hu n hn2) (by positivity)
    _ = a / 2 * Real.log n := by field_simp
    _ ≤ g n := by linarith [hl n hn2]

/-- The uniform ratio construction in dimension four. -/
theorem four_sparse_of_growth (hGrowth : Parking.External.SandpileGrowth) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ᶠ n : ℕ in atTop, c * Real.log (Real.exp 1 / ε) ≤
        meanU (law 4 (threePointLaw (ε / 2))) n /
          meanu (law 4 (threePointLaw (ε / 2))) n := by
  obtain ⟨a, ha, hcc⟩ := Parking.Frozen.cor_critical
  obtain ⟨C, hC, hu⟩ := exists_meanu_sparse_upper hGrowth
  refine ⟨a / (2 * C), by positivity, fun ε hε hε1 => ?_⟩
  have hν : CriticalLaw (threePointLaw (ε / 2)) :=
    criticalLaw_threePointLaw (by positivity) (by linarith)
  haveI := hν.prob
  obtain ⟨D, _hD, hl⟩ := hcc 4 (by norm_num) _ hν.prob hν.nonconst hν.integrable_abs hν.mean
  have hBP := hGrowth 4 (by norm_num) (realLaw (threePointLaw (ε / 2))) inferInstance
    (realLaw_mean _ hν) (realLaw_evariance_pos _ hν) (realLaw_evariance_lt_top _ hν)
    (realLaw_expMoment _ hν)
  obtain ⟨b, B, hb, _hB, hsp⟩ := hBP.2.1 rfl
  apply eventually_ratio_ge_log_scale
    (meanu (law 4 (threePointLaw (ε / 2)))) (meanU (law 4 (threePointLaw (ε / 2))))
    ha hC (log_exp_div_pos hε (by linarith))
  · intro n hn
    rw [meanu_eq_meanSandpileReal (by norm_num)]
    exact (mul_pos hb (log_pos_of_two_le hn)).trans_le (hsp n hn).1
  · exact hu ε hε hε1
  · exact fun n hn => (le_max_right _ _).trans (hl n hn)
end Parking
