/-
Summable logarithmic tails and almost-sure convergence.
-/
import Parking.Support.MomentTail
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Eventual domination by a summable nonnegative sequence implies summability. -/
theorem summable_of_eventually_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hg : Summable g) (hfg : ∀ᶠ n in atTop, f n ≤ g n) : Summable f := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfg
  rw [← summable_nat_add_iff N]
  apply Summable.of_nonneg_of_le (fun n => hf (n + N)) (fun n => hN (n + N) (by omega))
  exact (summable_nat_add_iff N).mpr hg

/-- The logarithmic Gaussian tail is summable. -/
theorem summable_exp_neg_log_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-(c * Real.log n ^ 2))) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply summable_of_eventually_le (fun n => (Real.exp_pos _).le)
    ((Real.summable_nat_rpow).mpr (by norm_num : (-2 : ℝ) < -1))
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 / c)), eventually_ge_atTop 2]
    with n hn hn2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnL : 0 ≤ Real.log n := (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  rw [div_le_iff₀ hc] at hn
  have h := mul_le_mul_of_nonneg_left hn hnL
  nlinarith only [h]

/-- Summable real event probabilities have a finite lower sum. -/
theorem tsum_measure_ne_top_of_summable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : ℕ → Set Ω)
    (hs : Summable (fun n => μ.real (s n))) : (∑' n, μ (s n)) ≠ ⊤ := by
  have h := ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg) hs
  simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  rw [← h]
  exact ENNReal.ofReal_ne_top

/-- Summable tails at every positive threshold give almost-sure convergence to zero. -/
theorem ae_tendsto_zero_of_summable_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ)
    (hs : ∀ ε : ℝ, 0 < ε → Summable (fun n => μ.real {ω | ε < |f n ω|})) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  have hae : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |f n ω| ≤ 1 / (k + 1 : ℝ) := by
    intro k
    have h := ae_eventually_notMem (μ := μ)
      (tsum_measure_ne_top_of_summable μ (fun n => {ω | 1 / (k + 1 : ℝ) < |f n ω|})
        (hs _ (by positivity)))
    simpa only [Set.mem_setOf_eq, not_lt] using h
  filter_upwards [ae_all_iff.mpr hae] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  exact ⟨N, fun n hn => by simpa only [Real.dist_eq, sub_zero] using (hN n hn).trans_lt hk⟩
end Parking
