import Parking.Support.NearestTwoHoleProof
import Parking.Support.NearestPairSum
import Parking.Support.MovingCutoff
import Parking.Support.FloorVolume
import Parking.Support.NearestDensityCriterion
import Parking.Support.HoleTail

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology

/-- Sparse critical holes retain a positive-density region closer to holes than to activity. -/
theorem nearest_counterexample_eventual (hBernstein : External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ t : ℕ in atTop, c ≤ ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC, hTwo⟩ := nearest_two_hole_proof hBernstein d hd
  obtain ⟨L, hL⟩ := exists_twoHole_inner_cutoff hd C
  let B : ℝ := ((2 * L + 1 : ℕ) : ℝ) ^ d
  have hB : 0 < B := by dsimp only [B]; positivity
  let p : ℝ := min (1 / 4) (1 / (32 * B))
  have hp : 0 < p := lt_min (by norm_num) (by positivity)
  have hp4 : p ≤ 1 / 4 := min_le_left _ _
  have hpB : 2 * p * B ≤ 1 / 16 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * B)).mp (min_le_right (1 / 4) (1 / (32 * B)))
    change p * (32 * B) ≤ 1 at h
    nlinarith
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI := stackRankLaw_isProbability hd1
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d (threePointLaw p)) :=
    inferInstanceAs (IsProbabilityMeasure ((iidLaw d (threePointLaw p)).prod (stackRankLaw d)))
  let k : ℝ := C * Real.exp 1
  let D : ℝ := ((8 * d + 1 : ℕ) : ℝ) ^ d
  have hk : 0 < k := mul_pos hC (Real.exp_pos _)
  have hD : 0 < D := by dsimp only [D]; positivity
  let b : ℝ := 1 / (16 * k * D)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hconst : k * D * b = 1 / 16 := by
    dsimp only [b]
    field_simp
  let h : ℕ → ℝ := holeProb d (threePointLaw p)
  have hh : ∀ t, 0 < h t := holeProb_pos hd1 hp hp4
  have hh1 : ∀ t, h t ≤ 1 := fun t => (holeProb_le_p hd1 hp hp4 t).trans (by linarith)
  have hlim : Tendsto h atTop (𝓝 0) := sparse_holeProb_tendsto_zero hBernstein hd hp hp4
  have hM := eventually_exists_middle_cutoff d hd C hC h hh hh1 hlim
  refine ⟨p, hp, by linarith, b / 4, by positivity, ?_⟩
  filter_upwards [hM, hlim.eventually (eventually_le_nhds hb)] with t ht htb
  obtain ⟨M, hfar, hmid⟩ := ht
  obtain ⟨R, hvol, houter⟩ := exists_radius_volume d hd1 hb (hh t) htb
  have htwo (z : Site d) (hz : z ≠ 0) :
      ((law d (threePointLaw p)) {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal ≤
      C * h t ^ 2 * Real.exp (C * Real.log (1 / h t) * (1 + (graphNorm z : ℝ)) ^ (4 - (d : ℝ))) := by
    have h0 := hTwo p hp hp4 t 0 z (Ne.symm hz)
    simpa only [zero_sub, graphNorm, Pi.neg_apply, Int.natAbs_neg] using h0
  have hs := nearest_pair_sum_bound hd hp hp4 hC t R L M htwo hL hfar
  have hsmall : B * (2 * p * h t) ≤ h t / 16 := by
    have h0 := mul_le_mul_of_nonneg_right hpB (hh t).le
    nlinarith
  have hlarge : ((8 * d * R + 1 : ℕ) : ℝ) ^ d * (k * (h t) ^ 2) ≤ h t / 16 := by
    have h0 := mul_le_mul_of_nonneg_right houter (mul_nonneg hk.le (hh t).le)
    have hcon := congrArg (fun u : ℝ => u * h t) hconst
    nlinarith
  have hpair : (∑ z ∈ (boxFinset (0 : Site d) (4 * d * R)).erase 0,
      ((law d (threePointLaw p)) {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal) ≤ h t / 4 := by
    change _ ≤ B * (2 * p * h t) + ((2 * M + 1 : ℕ) : ℝ) ^ d * (C * h t ^ (7 / 4 : ℝ)) +
      ((8 * d * R + 1 : ℕ) : ℝ) ^ d * (k * (h t) ^ 2) at hs
    linarith
  have hc := holeCloser_lower_of_pair_sum hd1 hp hp4 t R hpair
  have hbvol : b / 4 ≤ h t / 4 * ((R + 1 : ℕ) : ℝ) ^ d := by linarith
  exact hbvol.trans hc

/-- The nearest-hole counterexample in dimension at least five. -/
theorem nearest_counterexample_proof (hBernstein : External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ => ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal) atTop := by
  obtain ⟨p, hp, hp2, c, hc, he⟩ := nearest_counterexample_eventual hBernstein d hd
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI := stackRankLaw_isProbability (by omega : 1 ≤ d)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d (threePointLaw p)) :=
    inferInstanceAs (IsProbabilityMeasure ((iidLaw d (threePointLaw p)).prod (stackRankLaw d)))
  have hb : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun t : ℕ => ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal) := by
    refine ⟨1, ?_⟩
    change ∀ᶠ t : ℕ in atTop, ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal ≤ 1
    apply Eventually.of_forall
    intro t
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [ENNReal.ofReal_one, measure_univ] using
      (measure_mono (μ := law d (threePointLaw p)) (Set.subset_univ {ω : Data d | HoleCloser ω t}))
  exact ⟨p, hp, hp2, c, hc, le_liminf_of_le hb.isCoboundedUnder_ge he⟩

end Parking
