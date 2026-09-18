import Parking.Support.NoArrivalJoint
import Parking.Support.NoArrivalSplit
import Parking.Support.SinkLambdaMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The probability of no entrance to the sink decays exponentially in the ordinary mean odometer. -/
theorem exists_sparseSink_noArrival_bound (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ T : ℕ,
      (((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d))
        {z | noArrivalFlag (sparseSinkField T 0 z.1) 0 (curryRoundNoise z.2) T 0 = true}).toReal ≤
          A * Real.exp (-c * meanU (law d (threePointLaw p)) T) := by
  obtain ⟨C, hC, hmoment⟩ := exists_sparseSinkLambda_centered_moment hBernstein hd
  have hd1 : 1 ≤ d := by omega
  have hg : 1 ≤ escapeConst d := one_le_escapeConst (by omega)
  obtain ⟨A, c, hA, hc, htail⟩ := exists_exponential_lower_tail
    (Ω := (Site d → ℤ) × FlatRoundNoise d) hC hg
  have hg0 : 0 < escapeConst d := by linarith
  let c' := min c (1 / (2 * escapeConst d))
  refine ⟨A + 1, c', by linarith, lt_min hc (by positivity), fun p hp hp4 T => ?_⟩
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)
  let m := meanU (law d (threePointLaw p)) T
  let b := walkOp (sparseSinkMean (d := d) p T) 0
  let F : (Site d → ℤ) × FlatRoundNoise d → Bool :=
    fun z => noArrivalFlag (sparseSinkField T 0 z.1) 0 (curryRoundNoise z.2) T 0
  have hm : 0 ≤ m := integral_nonneg fun _ => Nat.cast_nonneg _
  have hF : Measurable F := measurable_noArrivalFlag_of hd1 _ _ _
    ((measurable_sparseSinkField T 0).comp measurable_fst) measurable_const
    (measurable_curryRoundNoise.comp measurable_snd) T 0
  have hW := measurable_noArrivalWeight_of hd1
    (fun z : (Site d → ℤ) × FlatRoundNoise d => sparseSinkField T 0 z.1) (fun _ => 0)
    (fun z => curryRoundNoise z.2) ((measurable_sparseSinkField T 0).comp measurable_fst)
    measurable_const (measurable_curryRoundNoise.comp measurable_snd) T 0
  have hiW : Integrable (fun z => if F z then Real.exp (sparseSinkLambda T z) else 0) μ :=
    Integrable.of_bound hW.aestronglyMeasurable _ (ae_of_all _ fun z =>
      noArrivalWeight_bound hd1 _ 1 (sparseSinkField_particle_bound T 0 z.1) 0 (curryRoundNoise z.2) T 0)
  have hIW : (∫ z, if F z then Real.exp (sparseSinkLambda T z) else 0 ∂μ) ≤ 1 :=
    integral_noArrivalWeight_prod_le_one hd1 (iidLaw d (threePointLaw p)) (sparseSinkField T 0)
      (measurable_sparseSinkField T 0) 1 (sparseSinkField_particle_bound T 0) 0 T 0
  have hs := measure_flag_le_lower_tail μ F (sparseSinkLambda T) hF (measurable_sparseSinkLambda hd1 T)
    hiW hIW (m / (2 * escapeConst d))
  have hTail := htail μ inferInstance (sparseSinkLambda T) m b hm
    (sparseSink_compensator_mean_bounds (by omega) hp hp4 T).1
    (fun r hr => integrable_abs_rpow_bounded μ (fun z => sparseSinkLambda T z - b)
      ((measurable_sparseSinkLambda hd1 T).sub_const b) _
      (fun z => (abs_sub _ _).trans (add_le_add (sparseSinkLambda_bound hd1 T z) (le_refl _))) (by linarith))
    (fun r hr => hmoment p hp hp4 T r hr)
  have he₁ : Real.exp (-c * m) ≤ Real.exp (-c' * m) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg
      (mul_le_mul_of_nonneg_right (min_le_left c (1 / (2 * escapeConst d))) hm)
  have he₂ : Real.exp (-(m / (2 * escapeConst d))) ≤ Real.exp (-c' * m) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right c (1 / (2 * escapeConst d))) hm
    have he : 1 / (2 * escapeConst d) * m = m / (2 * escapeConst d) := by ring
    rw [he] at h
    simpa only [neg_mul] using neg_le_neg h
  exact hs.trans ((add_le_add hTail (le_refl _)).trans (by
    nlinarith [mul_le_mul_of_nonneg_left he₁ hA.le]))
end Parking
