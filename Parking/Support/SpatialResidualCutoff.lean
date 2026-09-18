/- Vanishing mean of bounded residual tests on the discrete positive region. -/
import Parking.Support.SpatialResidualEstimate
import Parking.Support.SpatialSceneryAlgebra
import Parking.Generic.LocalResidual

open MeasureTheory Set Filter Topology LatticeProb
open Parking.Generic.PositiveCutoff Parking.Generic.LocalResidual
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The parabolic field has a measurable positivity cutoff on every set. -/
theorem measurable_cutoff_barDivisible (K : Set (ℝ × (Fin d → ℝ))) (δ R : ℝ) :
    Measurable (fun w : Data d => cutoff K δ (fun p => barDivisible w R p.1 p.2)) :=
  measurable_cutoff_countable K (fun p => (⌊p.1 * R ^ 2⌋₊, latticePoint R p.2)) δ
    (fun w q => R ^ ((d : ℝ) / 2 - 2) * uOf w q.1 q.2)
    (fun q => (measurable_uOf q.1 q.2).const_mul _)

theorem measurable_discreteResidualTest
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ)
    (K : Set (ℝ × (Fin d → ℝ))) (δ R : ℝ) :
    Measurable (fun w : Data d => test volume K (tsupport ψ) δ (spaceTimeResidualTest ψ)
      (scenePair w R (fun x => ∫ s : ℝ, ψ (s, x))) (fun p => barDivisible w R p.1 p.2)) := by
  exact (measurable_cutoff_barDivisible (tsupport ψ) δ R).mul (measurable_const.min
    ((measurable_integral_spaceTime_barDivisible_mul R K _
      (continuous_spaceTimeResidualTest hψ).measurable).sub (measurable_scenePair_any_R R)).abs)

/-- The discrete weak residual vanishes in mean after multiplication by the positivity cutoff. -/
theorem tendsto_integral_discreteResidualTest_zero (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ)
    {a B T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hlow : ∀ s x, s < 2 * a → ψ (s, x) = 0)
    (hhigh : ∀ s x, T ≤ s → ψ (s, x) = 0)
    (hb : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ B)
    (hsource : Tendsto (fun R : ℝ => ∫ w,
      |scenePair w R (fun x => sampledTimeIntegral ψ T R x - ∫ s : ℝ, ψ (s, x))|
        ∂law d ν) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R : ℝ => ∫ w,
      test volume (Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2)) (tsupport ψ) δ
        (spaceTimeResidualTest ψ) (scenePair w R (fun x => ∫ s : ℝ, ψ (s, x)))
        (fun p => barDivisible w R p.1 p.2) ∂law d ν) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  let K : Set (ℝ × (Fin d → ℝ)) := Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  let F : ℝ → Data d → ℝ := fun R w => test volume K (tsupport ψ) δ
    (spaceTimeResidualTest ψ) (scenePair w R (fun x => ∫ s : ℝ, ψ (s, x)))
      (fun p => barDivisible w R p.1 p.2)
  let Y : ℝ → Data d → ℝ := fun R w => ∫ p in K, barDivisible w R p.1 p.2
  let E : ℝ → Data d → ℝ := fun R w =>
    |scenePair w R (fun x => sampledTimeIntegral ψ T R x - ∫ s : ℝ, ψ (s, x))|
  obtain ⟨C, hC, hmass⟩ := exists_integral_local_spaceTime_barDivisible_le hd hd3 hGrowth ν hν K hK
  have hFI : ∀ R, Integrable (F R) (law d ν) := by
    intro R
    apply Integrable.of_bound (measurable_discreteResidualTest hψ K δ R).aestronglyMeasurable 1
    exact ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (test_nonneg _ _ _ _ _ _ _)]
      exact test_le_one _ _ _ _ _ _ _
  have hEI : ∀ R, 1 ≤ R → Integrable (E R) (law d ν) := by
    intro R hR
    have ht := isTestFun_sampledTimeIntegral hψ T R
    have hi := isTestFun_timeIntegral hψ
    exact (integrable_scenePair_test hd ν hν.integrable_abs ⟨ht.1.sub hi.1, ht.2.sub hi.2⟩ hR).abs
  have hdom : ∀ η : ℝ, 0 < η → ∀ᶠ R : ℝ in atTop, ∀ w, F R w ≤ η * Y R w + E R w := by
    intro η hη
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_abs_discreteResidual_le hd hψ ha hT hlow hhigh hb hη] with R hR herr w
    have hY : 0 ≤ Y R w := integral_nonneg fun p =>
      barDivisible_nonneg w (le_trans zero_le_one hR) _ _
    by_cases hz : cutoff (tsupport ψ) δ (fun p => barDivisible w R p.1 p.2) = 0
    · change test _ _ _ _ _ _ _ ≤ _
      rw [test, hz, zero_mul]
      exact add_nonneg (mul_nonneg hη.le hY) (abs_nonneg _)
    have hp := positive_of_cutoff_ne_zero hδ hz
    have he := herr w hp
    have heS := scenePair_sub_test w (isTestFun_sampledTimeIntegral hψ T R) (isTestFun_timeIntegral hψ) hR
    have htest : F R w ≤ |(∫ p in K, barDivisible w R p.1 p.2 * spaceTimeResidualTest ψ p) -
        scenePair w R (fun x => ∫ s : ℝ, ψ (s, x))| := by
      exact (mul_le_mul (cutoff_le_one _ _ _) (min_le_right _ _)
        (le_min zero_le_one (abs_nonneg _)) zero_le_one).trans_eq (one_mul _)
    apply htest.trans
    calc
      _ ≤ |(∫ p in K, barDivisible w R p.1 p.2 * spaceTimeResidualTest ψ p) -
          scenePair w R (sampledTimeIntegral ψ T R)| +
          |scenePair w R (sampledTimeIntegral ψ T R) - scenePair w R (fun x => ∫ s : ℝ, ψ (s, x))| := abs_sub_le _ _ _
      _ ≤ η * Y R w + E R w := by rw [← heS]; exact add_le_add he le_rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (2 * (C + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), hdom η hη,
    (tendsto_order.mp hsource).2 (ε / 2) (half_pos hε)] with R hR hdomR hER
  have hRI : 1 ≤ R := by linarith
  have hi := (hmass R hR).2.1
  have hm := (hmass R hR).2.2
  have hle : (∫ w, F R w ∂law d ν) ≤ η * C + ∫ w, E R w ∂law d ν := by
    calc
      _ ≤ ∫ w, η * Y R w + E R w ∂law d ν :=
        integral_mono (hFI R) ((hi.const_mul η).add (hEI R hRI)) hdomR
      _ = η * (∫ w, Y R w ∂law d ν) + ∫ w, E R w ∂law d ν := by
        rw [integral_add (hi.const_mul η) (hEI R hRI), integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm hη.le) le_rfl
  have hsmall : η * C < ε / 2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * (C + 1))]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun w => test_nonneg _ _ _ _ _ _ _)]
  exact hle.trans_lt (by change (∫ w, E R w ∂law d ν) < ε / 2 at hER; linarith)

end Parking
