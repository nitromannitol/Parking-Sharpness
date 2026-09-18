import Parking.Support.TwoHoleLoadMoment
import Parking.Support.LogMomentTail
import Parking.Support.TwoHoleConstants
import Parking.Support.DiscountSplit
import Parking.Support.HoleKernelBound
import Parking.Support.HoleTail
import LatticeProb.Walk.RangeSecond

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- The two-hole bound follows from the actual reveal factors and the one-point moments. -/
theorem nearest_two_hole_proof (hBernstein : External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 →
      ∀ (t : ℕ) (x z : Site d), x ≠ z →
        ((law d (threePointLaw p)) {ω | H ω t x = 1 ∧ H ω t z = 1}).toReal ≤
          C * holeProb d (threePointLaw p) t ^ 2 * Real.exp (C * Real.log (1 / holeProb d (threePointLaw p) t)
            * (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  obtain ⟨Cu, hCu, hMoment⟩ := exists_twoHoleLoad_moment_bound hBernstein hd
  obtain ⟨Cm, hCm, hMean⟩ := exists_sparse_mean_log_bound hBernstein hd
  obtain ⟨Cb, hCb, hBubble⟩ := exists_holeKernel_sum_bound hd
  obtain ⟨A, hA, hTail⟩ := exists_log_moment_upper_tail Cu Cm hCu hCm
  let Ci : ℝ := 1 / (1 / (2 * escapeConst d)) ^ 2
  have hCi : 0 < Ci := by
    dsimp only [Ci]
    have hg : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd3)
    positivity
  obtain ⟨C, hC, hFinal⟩ := exists_two_hole_constant_assembly Cb (holeSceneryConst d) Ci A
    hCb (holeSceneryConst_pos hd3) hCi hA
  refine ⟨C, hC, fun p hp hp4 T x z hxz => ?_⟩
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := roundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (roundNoiseLaw d)
  let h := holeProb d (threePointLaw p) T
  let m := meanU (law d (threePointLaw p)) T
  let b := (1 + (graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ))
  have hh : 0 < h := holeProb_pos hd1 hp hp4 T
  have hh4 : h ≤ 1 / 4 := (holeProb_le_p hd1 hp hp4 T).trans hp4
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  let R := T + graphNorm (x - z)
  have hxR : boxFinset x T ⊆ boxFinset x R := boxFinset_mono (by dsimp only [R]; omega)
  have hzR : boxFinset z T ⊆ boxFinset x R := by
    have hz : z ∈ boxFinset x (graphNorm (x - z)) := by
      rw [graphNorm_eq_srw]
      exact mem_boxFinset_of_graphNorm_sub_le le_rfl
    intro y hy
    simpa only [R, Nat.add_comm] using mem_boxFinset_add hz hy
  have hSc : (∑ y ∈ boxFinset x R, (1 - escapePotential d x y) * (1 - escapePotential d z y)) ≤ Cb * b :=
    (hBubble x z (boxFinset x R)).1
  have hSk : (∑ y ∈ boxFinset x R, holeKernel d x z y) ≤ Cb * b := (hBubble x z (boxFinset x R)).2
  have ht := hTail μ (twoHoleLoad T x z x R) (twoHoleLoad_nonneg hd3 T x z x R)
    h m (Cb * b) hh (hh4.trans (by norm_num)) (mul_pos hCb hb) (hMean p hp hp4 T)
    (fun r hr => hMoment p hp hp4 T x z x R (Cb * b) hSk r hr)
  have hdisc := integral_twoHoleDiscount_le hd3 (threePointLaw p) (ae_clipSparse_threePointLaw p) T x z x hxz R hxR hzR
  have hdisc' : (∫ ω, twoHoleDiscount T x z x R ω ∂μ) ≤ Real.exp (holeSceneryConst d * (Cb * b)) * h ^ 2 :=
    hdisc.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hSc (holeSceneryConst_pos hd3).le)) (sq_nonneg h))
  have hi : Integrable (twoHoleDiscount T x z x R) μ :=
    Integrable.of_bound (measurable_twoHoleDiscount hd1 T x z x R).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (twoHoleDiscount_bounds hd3 T x z x R ω).1]
        exact (twoHoleDiscount_bounds hd3 T x z x R ω).2)
  let E := {ω : (Site d → ℤ) × RoundNoise d | clippedRoundH T x ω = 1 ∧ clippedRoundH T z ω = 1}
  have hE : MeasurableSet E :=
    ((measurable_clippedRoundH hd1 T x) (measurableSet_singleton 1)).inter
      ((measurable_clippedRoundH hd1 T z) (measurableSet_singleton 1))
  have hED (ω : (Site d → ℤ) × RoundNoise d) (hω : ω ∈ E) :
      twoHoleDiscount T x z x R ω = Real.exp (-Ci * twoHoleLoad T x z x R ω) := by
    rcases hω with ⟨hx, hz⟩
    simp only [twoHoleDiscount, hx, hz, Nat.cast_one, one_mul]
    congr 1
    dsimp only [Ci]
    ring
  have hs := measure_event_le_discount_tail μ E hE (twoHoleLoad T x z x R)
    (measurable_twoHoleLoad hd1 T x z x R) Ci hCi.le (twoHoleDiscount T x z x R)
    (fun ω => (twoHoleDiscount_bounds hd3 T x z x R ω).1) hi hED
    (Real.exp (holeSceneryConst d * (Cb * b)) * h ^ 2) hdisc' (A * (1 + Real.log (1 / h)) * (Cb * b))
  have hP := hs.trans (add_le_add le_rfl ht)
  have hpair : (μ E).toReal = ((law d (threePointLaw p)) {ω | H ω T x = 1 ∧ H ω T z = 1}).toReal :=
    clippedRoundH_pair_probability hd1 _ (ae_clipSparse_threePointLaw p) T x z
  rw [hpair] at hP
  exact hFinal h b _ hh hh4 hb.le hP
end Parking
