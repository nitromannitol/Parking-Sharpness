import Parking.Support.TableBernstein
import Parking.Support.BoundedConditionalMoment
import Parking.Support.ProductLift

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- The conditional instruction estimate integrates over any bounded random initial field. -/
theorem exists_table_joint_noise_moment_bound (hBernstein : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 3 ≤ d → ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (Φ : Ω → Site d → ℤ), Measurable Φ →
      (∀ ω y, (Φ ω y).toNat ≤ 1) → ∀ (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
      rNorm (μ.prod (flatRoundNoiseLaw d)) r
          (fun z => ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x : ℝ) -
            matchedMeanU (Φ z.1) ρ T x) ≤
        C * (Real.sqrt r * (∫ z, greenWeightedOdometer (Φ z.1) ρ (curryRoundNoise z.2) T x T ^ (r / 2)
          ∂(μ.prod (flatRoundNoiseLaw d))) ^ (1 / r) + r * escapeConst d) := by
  obtain ⟨C, hC, hb⟩ := exists_table_noise_moment_bound hBernstein
  refine ⟨C, hC, fun d hd Ω mΩ μ hμ Φ hΦ hΦb ρ T x r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hr0 : 0 < r := by linarith
  haveI := flatRoundNoiseLaw_isProbability hd1
  let ν := flatRoundNoiseLaw d
  let B : ℝ := ((T * (2 * T + 1) ^ d : ℕ) : ℝ)
  let W : ℝ := ∑ v ∈ boxFinset x T, walkOp (fun y => fullGreen d (y - x) ^ 2) v
  let F : Ω × FlatRoundNoise d → ℝ := fun z =>
    ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x : ℝ) - matchedMeanU (Φ z.1) ρ T x
  let Q : Ω × FlatRoundNoise d → ℝ := fun z => greenWeightedOdometer (Φ z.1) ρ (curryRoundNoise z.2) T x T
  let Y : Ω → ℝ := fun ω => (∫ ξ, Q (ω, ξ) ^ (r / 2) ∂ν) ^ (1 / r)
  have hS := measurableState_matchedState ⟨0, hd1⟩ (fun z : Ω × FlatRoundNoise d => Φ z.1)
    (fun _ => ρ) (fun z => curryRoundNoise z.2) (hΦ.comp measurable_fst)
    measurable_const (measurable_curryRoundNoise.comp measurable_snd) T
  have hU (v : Site d) : Measurable (fun z : Ω × FlatRoundNoise d =>
      ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures v : ℝ)) :=
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 v)
  have hM : Measurable (fun z : Ω × FlatRoundNoise d => matchedMeanU (Φ z.1) ρ T x) :=
    (measurable_matchedMeanU hd1 ρ T x).comp (hΦ.comp measurable_fst)
  have hF : Measurable F := (hU x).sub hM
  have hQ : Measurable Q := Finset.measurable_sum _ fun v _ => (hU v).const_mul _
  have hQ0 (z : Ω × FlatRoundNoise d) : 0 ≤ Q z := greenWeightedOdometer_nonneg _ _ _ _ _ _
  have hQB (z : Ω × FlatRoundNoise d) : Q z ≤ W * B :=
    greenWeightedOdometer_le_box _ (hΦb z.1) ρ _ T x T
  have hFB (z : Ω × FlatRoundNoise d) : |F z| ≤ 2 * B := by
    have hu : ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x : ℝ) ≤ B := by
      exact Nat.cast_le.mpr (by simpa only [mul_one] using matchedOdometer_le_box _ 1 (hΦb z.1) ρ _ T x)
    have hm : matchedMeanU (Φ z.1) ρ T x ≤ B := by
      simpa only [mul_one] using matchedMeanU_le_box hd1 (Φ z.1) 1 (hΦb z.1) ρ T x
    exact abs_le.mpr ⟨by dsimp only [F]; linarith [Nat.cast_nonneg (α := ℝ) ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x)],
      by dsimp only [F]; linarith [matchedMeanU_nonneg (Φ z.1) ρ T x]⟩
  have hY := bounded_conditional_moment_root ν Q hQ hQ0 (W * B) hQB (by linarith : 0 ≤ r / 2) hr0
  have hi := integrable_abs_rpow_bounded (μ.prod ν) F hF (2 * B) hFB hr0.le
  have hQi := integrable_rpow_bounded_nonneg (μ.prod ν) Q hQ hQ0 (W * B) hQB (by linarith : 0 ≤ r / 2)
  have hcond (ω : Ω) : rNorm ν r (fun ξ => F (ω, ξ)) ≤ (C * Real.sqrt r) * Y ω + C * (r * escapeConst d) := by
    have h := hb d hd (Φ ω) (hΦb ω) ρ T x r hr
    convert h using 1
    dsimp only [F, Y, Q, ν]
    ring
  have hlift := rNorm_prod_le_of_conditional μ ν F Y hY.1 (fun ω => (hY.2 ω).1)
    (((W * B) ^ (r / 2)) ^ (1 / r)) (fun ω => (hY.2 ω).2) (by linarith : 1 ≤ r) hi
    (mul_nonneg hC.le (Real.sqrt_nonneg r))
    (mul_nonneg hC.le (mul_nonneg hr0.le (zero_le_one.trans (one_le_escapeConst hd)))) hcond
  have heY := rNorm_integral_root μ ν Q hQ0 hr0 hQi
  change rNorm μ r Y = _ at heY
  rw [heY] at hlift
  convert hlift using 1
  ring
end Parking
