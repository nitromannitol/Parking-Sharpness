import Parking.Support.WeightedOdometerBounds
import Parking.Support.ProductLift

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Minkowski separates the initial field and the instructions in a bounded table process. -/
theorem table_moment_decomposition (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Φ : Ω → Site d → ℤ) (hΦ : Measurable Φ)
    (hΦb : ∀ ω y, (Φ ω y).toNat ≤ 1) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    {r : ℝ} (hr : 1 ≤ r) :
    rNorm (μ.prod (flatRoundNoiseLaw d)) r
        (fun z => ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x : ℝ)) ≤
      rNorm μ r (fun ω => matchedMeanU (Φ ω) ρ T x) +
        rNorm (μ.prod (flatRoundNoiseLaw d)) r
          (fun z => ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x : ℝ) -
            matchedMeanU (Φ z.1) ρ T x) := by
  haveI := flatRoundNoiseLaw_isProbability hd
  let ν := flatRoundNoiseLaw d
  let B : ℝ := ((T * (2 * T + 1) ^ d : ℕ) : ℝ)
  let M : Ω → ℝ := fun ω => matchedMeanU (Φ ω) ρ T x
  let U' : Ω × FlatRoundNoise d → ℝ := fun z => ((matchedState (Φ z.1) ρ (curryRoundNoise z.2) T).departures x : ℝ)
  have hr0 : 0 < r := by linarith
  have hM : Measurable M := (measurable_matchedMeanU hd ρ T x).comp hΦ
  have hM0 (ω : Ω) : 0 ≤ M ω := matchedMeanU_nonneg _ _ _ _
  have hMB (ω : Ω) : |M ω| ≤ B := by
    rw [abs_of_nonneg (hM0 ω)]
    simpa only [mul_one] using matchedMeanU_le_box hd (Φ ω) 1 (hΦb ω) ρ T x
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun z : Ω × FlatRoundNoise d => Φ z.1)
    (fun _ => ρ) (fun z => curryRoundNoise z.2) (hΦ.comp measurable_fst)
    measurable_const (measurable_curryRoundNoise.comp measurable_snd) T
  have hU : Measurable U' := (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 x)
  have hUB (z : Ω × FlatRoundNoise d) : |U' z| ≤ B := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (by simpa only [mul_one] using matchedOdometer_le_box _ 1 (hΦb z.1) ρ _ T x)
  have hdiff (z : Ω × FlatRoundNoise d) : |U' z - M z.1| ≤ B + B := by
    calc
      _ ≤ |U' z| + |-M z.1| := abs_add_le _ _
      _ ≤ B + B := by rw [abs_neg]; exact add_le_add (hUB z) (hMB z.1)
  have hadd := rNorm_bounded_add_le (μ.prod ν) hr (fun z => M z.1) (fun z => U' z - M z.1)
    (hM.comp measurable_fst) (hU.sub (hM.comp measurable_fst)) B (B + B)
    (fun z => hMB z.1) hdiff
  have he : (fun z : Ω × FlatRoundNoise d => M z.1 + (U' z - M z.1)) = U' := funext fun _ => by ring
  rw [he] at hadd
  have hi := integrable_abs_rpow_bounded (μ.prod ν) (fun z => M z.1)
    (hM.comp measurable_fst) B (fun z => hMB z.1) hr0.le
  have hmnorm : rNorm (μ.prod ν) r (fun z => M z.1) = rNorm μ r M := by
    rw [rNorm_prod μ ν _ hr0 hi]
    congr 1
    funext ω
    exact rNorm_const ν hr0 (hM0 ω)
  rw [hmnorm] at hadd
  exact hadd
end Parking
