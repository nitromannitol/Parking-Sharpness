import Parking.Support.SinkGreenMoment
import Parking.Support.OnePointMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Instruction fluctuations of every sink odometer have the Bernstein moment scale. -/
theorem exists_sparseSink_noise_moment (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (v x : Site d) (r : ℝ), 2 ≤ r →
      rNorm ((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) r
        (fun z => sparseSinkTableU T v x z - matchedMeanU (sparseSinkField T v z.1) 0 T x) ≤
          C * (Real.sqrt (r * (meanU (law d (threePointLaw p)) T + r)) + r) := by
  obtain ⟨Cb, hCb, hb⟩ := exists_table_joint_noise_moment_bound hBernstein
  obtain ⟨W, hW, hw⟩ := exists_clipped_green_moment_bound hd
  obtain ⟨Cu, hCu, hu⟩ := exists_sparse_odometer_moment_bound hBernstein hd
  have hd1 : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  have hg : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd3)
  let a := Real.sqrt (W * Cu)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  refine ⟨Cb * (a + escapeConst d), mul_pos hCb (by linarith), fun p hp hp4 T v x r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)
  let m := meanU (law d (threePointLaw p)) T
  let X := rNorm μ r (clippedTableU T 0)
  have hm : 0 ≤ m := integral_nonneg fun _ => Nat.cast_nonneg _
  have hX : 0 ≤ X := rNorm_nonneg _ _ _
  have hXu : X ≤ Cu * (m + r) := by
    dsimp only [X, μ]
    rw [rNorm_clippedTableU hd1 _ (ae_clipSparse_threePointLaw p) T 0 hr0.le]
    have he : rNorm (law d (threePointLaw p)) r (fun ω => (U ω T 0 : ℝ)) =
        (∫ ω, (U ω T 0 : ℝ) ^ r ∂(law d (threePointLaw p))) ^ (1 / r) := by
      unfold rNorm
      have habs (ω : Data d) : |(U ω T 0 : ℝ)| = (U ω T 0 : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      simp only [habs]
    rw [he]
    exact (hu p hp hp4 T 0 r hr).2
  have hQ := (sparseSink_green_moment_le hd1 (threePointLaw p) T v x hr0).trans (hw p hp hp4 T x r hr)
  have hroot : Real.sqrt (W * X) ≤ Real.sqrt (W * (Cu * (m + r))) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hXu hW.le)
  have hQ' := hQ.trans hroot
  have hnoise := hb d hd3 (Site d → ℤ) (iidLaw d (threePointLaw p)) (sparseSinkField T v)
    (measurable_sparseSinkField T v) (sparseSinkField_particle_bound T v) 0 T x r hr
  have h := hnoise.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hQ' (Real.sqrt_nonneg r)) le_rfl) hCb.le)
  have he : Real.sqrt r * Real.sqrt (W * (Cu * (m + r))) = a * Real.sqrt (r * (m + r)) := by
    dsimp only [a]
    rw [← Real.sqrt_mul hr0.le, ← Real.sqrt_mul (mul_nonneg hW.le hCu.le)]
    congr 1
    ring
  rw [he] at h
  exact h.trans (by nlinarith [mul_nonneg ha hr0.le, mul_nonneg hg.le (Real.sqrt_nonneg (r * (m + r)))])
end Parking
