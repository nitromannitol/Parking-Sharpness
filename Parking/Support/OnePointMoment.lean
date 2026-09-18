import Parking.Support.TableJointNoise
import Parking.Support.TableDecomposition
import Parking.Support.ClippedGreenMoment
import Parking.Support.ClippedScenery

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The high-dimensional sparse odometer has every finite moment, with the paper's linear moment bound. -/
theorem exists_sparse_odometer_moment_bound (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
      Integrable (fun ω => (U ω T x : ℝ) ^ r) (law d (threePointLaw p)) ∧
        (∫ ω, (U ω T x : ℝ) ^ r ∂(law d (threePointLaw p))) ^ (1 / r) ≤
          C * (meanU (law d (threePointLaw p)) T + r) := by
  obtain ⟨Cb, hCb, hb⟩ := exists_table_joint_noise_moment_bound hBernstein
  obtain ⟨Cs, hCs, hs⟩ := exists_clipped_scenery_norm_bound hd
  obtain ⟨W, hW, hw⟩ := exists_clipped_green_moment_bound hd
  have hd1 : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  have hg : 0 ≤ escapeConst d := zero_le_one.trans (one_le_escapeConst hd3)
  let A : ℝ := 2 * Cs + Cb ^ 2 * W + 2 * Cb * escapeConst d
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨2 + A, by linarith, fun p hp hp4 T x r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)
  let X := rNorm μ r (clippedTableU T 0)
  let m := meanU (law d (threePointLaw p)) T
  have hm : 0 ≤ m := integral_nonneg fun _ => Nat.cast_nonneg _
  have hX : 0 ≤ X := rNorm_nonneg _ _ _
  have hdec := table_moment_decomposition hd1 (iidLaw d (threePointLaw p)) clippedField
    measurable_clippedField clippedField_particle_bound 0 T 0 hr1
  have hsc := hs p hp hp4 T 0 r hr
  have hnoise := hb d hd3 (Site d → ℤ) (iidLaw d (threePointLaw p)) clippedField
    measurable_clippedField clippedField_particle_bound 0 T 0 r hr
  have hweight := hw p hp hp4 T 0 r hr
  have hn : rNorm μ r (fun z => clippedTableU T 0 z - matchedMeanU (clippedField z.1) 0 T 0) ≤
      Cb * (Real.sqrt r * Real.sqrt (W * X) + r * escapeConst d) := by
    exact hnoise.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hweight (Real.sqrt_nonneg r)) le_rfl) hCb.le)
  have hbefore : X ≤ m + Cs * Real.sqrt r + Cb * (Real.sqrt ((r * W) * X) + r * escapeConst d) := by
    have hsqrt : Real.sqrt ((r * W) * X) = Real.sqrt r * Real.sqrt (W * X) := by
      rw [mul_assoc, Real.sqrt_mul hr0.le]
    rw [hsqrt]
    exact hdec.trans (add_le_add hsc hn)
  have hyoung := young_absorb hX (mul_nonneg hr0.le hW.le) hbefore
  have hsr : Real.sqrt r ≤ r := by
    nlinarith [Real.sq_sqrt hr0.le, Real.sqrt_nonneg r]
  have hlinear : X ≤ 2 * m + A * r := by
    dsimp only [A]
    nlinarith [mul_le_mul_of_nonneg_left hsr hCs.le]
  have hfinal : X ≤ (2 + A) * (m + r) := hlinear.trans (by nlinarith [mul_nonneg hA hm])
  refine ⟨integrable_U_rpow hd1 _ (by norm_num : (0 : ℝ) < 1) (integrable_threePointLaw p _) hr1 T x, ?_⟩
  have hnorm : (∫ ω, (U ω T x : ℝ) ^ r ∂(law d (threePointLaw p))) ^ (1 / r) =
      rNorm μ r (clippedTableU T x) := by
    rw [rNorm_clippedTableU hd1 _ (ae_clipSparse_threePointLaw p) T x hr0.le]
    unfold rNorm
    have habs (ω : Data d) : |(U ω T x : ℝ)| = (U ω T x : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    simp only [habs]
  rw [hnorm, rNorm_clippedTableU_shift hd1 hp hp4 T x hr1]
  exact hfinal
end Parking
