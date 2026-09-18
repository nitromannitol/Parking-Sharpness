/-
Relative discrepancy convergence in every moment and almost surely.
-/
import Parking.Support.DiscrepancyTail
import Parking.Support.MomentLimits
import Parking.Support.TailLimits

noncomputable section
namespace Parking
open MeasureTheory Filter
open scoped Topology

/-- The discrepancy divided by the mean sandpile odometer tends to zero in every fixed moment. -/
theorem discrepancy_moment_tendsto_zero {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) (q : ℝ) (hq : 1 ≤ q) :
    (∀ n : ℕ, Integrable (fun ω => |((U ω n 0 : ℝ) - uOf ω n 0) /
      meanu (law d ν) n| ^ q) (law d ν)) ∧
    Tendsto (fun n : ℕ => ∫ ω, |((U ω n 0 : ℝ) - uOf ω n 0) /
      meanu (law d ν) n| ^ q ∂(law d ν)) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  have hi := fun n => integrable_diff_rpow hd ν hθ hexp hq n
  refine ⟨fun n => integrable_abs_div_rpow (hi n) _, ?_⟩
  have hrel := eventually_discrepancy_relative_norm hd hd3 hGrowth hBern hConc hGN ν hν 1
    (by norm_num)
  simp only [one_mul] at hrel
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∫ ω, |((U ω n 0 : ℝ) - uOf ω n 0) / meanu (law d ν) n| ^ q ∂(law d ν)) ≤
        (n : ℝ) ^ (-((1 : ℝ) / 16 * q)) := by
    filter_upwards [hrel, hlog.eventually (eventually_ge_atTop q)] with n hn hqn
    have hqr : q ≤ rHigh n := hqn.trans hn.2.2
    have hmono := rNorm_mono_exponent (law d ν) hq hqr
      (fun ω => (U ω n 0 : ℝ) - uOf ω n 0)
      ((((measurable_from_countable' (fun k : ℕ => (k : ℝ))).comp
        (measurable_U n 0)).sub (measurable_uOf n 0)).aestronglyMeasurable)
      (hi n) (integrable_diff_rpow hd ν hθ hexp (hq.trans hqr) n)
    have hnorm : rNorm (law d ν) q (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) /
        meanu (law d ν) n ≤ (n : ℝ) ^ (-((1 : ℝ) / 16)) :=
      (div_le_div_of_nonneg_right hmono hn.2.1.le).trans hn.1
    rw [integral_abs_div_rpow (law d ν) (by linarith : 0 < q) _ hn.2.1.le]
    calc (rNorm (law d ν) q (fun ω => (U ω n 0 : ℝ) - uOf ω n 0) / meanu (law d ν) n) ^ q ≤
        ((n : ℝ) ^ (-((1 : ℝ) / 16))) ^ q :=
          Real.rpow_le_rpow (div_nonneg (rNorm_nonneg _ _ _) hn.2.1.le) hnorm (by linarith)
      _ = _ := by rw [← Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; ring
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) q) hbound
    ((tendsto_rpow_neg_atTop (by positivity : 0 < (1 : ℝ) / 16 * q)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- The summable discrepancy tails give almost-sure relative convergence. -/
theorem ae_discrepancy_tendsto_zero {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∀ᵐ ω ∂(law d ν), Tendsto (fun n : ℕ => ((U ω n 0 : ℝ) - uOf ω n 0) /
      meanu (law d ν) n) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  apply ae_tendsto_zero_of_summable_tails
  intro ε hε
  obtain ⟨c, hc, N, hN⟩ := exists_discrepancy_tail hd hd3 hGrowth hBern hConc hGN ν hν ε hε
  have hrel := eventually_discrepancy_relative_norm hd hd3 hGrowth hBern hConc hGN ν hν 1
    (by norm_num)
  simp only [one_mul] at hrel
  apply summable_of_eventually_le (fun n => measureReal_nonneg) (summable_exp_neg_log_sq hc)
  filter_upwards [hrel, eventually_ge_atTop N] with n hn hnN
  have heq : {ω : Data d | ε < |((U ω n 0 : ℝ) - uOf ω n 0) / meanu (law d ν) n|} =
      {ω : Data d | ε * meanu (law d ν) n < |(U ω n 0 : ℝ) - uOf ω n 0|} := by
    ext ω
    simp only [Set.mem_setOf_eq, abs_div, abs_of_pos hn.2.1, lt_div_iff₀ hn.2.1]
  rw [heq]
  exact hN n hnN
end Parking
