import Parking.Support.IsolatedDensity
import Parking.Support.SafeDensity
import Parking.Support.IsolationUnion
import Parking.Support.SparseActivity

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A small pair sum leaves a macroscopic region closer to surviving holes. -/
theorem holeCloser_lower_of_pair_sum (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (t R : ℕ)
    (hpair : (∑ z ∈ (boxFinset (0 : Site d) (4 * d * R)).erase 0,
      ((law d (threePointLaw p)) {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal) ≤
        holeProb d (threePointLaw p) t / 4) :
    holeProb d (threePointLaw p) t / 4 * ((R + 1 : ℕ) : ℝ) ^ d ≤
      ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI := stackRankLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d (threePointLaw p)) :=
    inferInstanceAs (IsProbabilityMeasure ((iidLaw d (threePointLaw p)).prod (stackRankLaw d)))
  let μ := law d (threePointLaw p)
  let h := holeProb d (threePointLaw p) t
  have hIso := measure_hole_le_isolated_add_pairs μ t (4 * d * R)
  have hIso' : (3 / 4 : ℝ) * h ≤ (μ {ω | IsolatedHole ω t (4 * d * R) 0}).toReal := by
    change h ≤ _ at hIso
    change _ ≤ h / 4 at hpair
    linarith
  obtain ⟨hiA, hA⟩ := sparse_activity_mean hd hp hp4 t
  have hGood := measure_isolated_le_good_add_activity hd (threePointLaw p) t (2 * d * R) hiA
  have hrad : 2 * (2 * d * R) = 4 * d * R := by ring
  have hGood' : (μ {ω | IsolatedHole ω t (4 * d * R) 0}).toReal ≤
      (μ {ω | GoodHole ω t R 0}).toReal + h / 2 := by
    rw [hrad, hA] at hGood
    simpa only [GoodHole, div_eq_mul_inv, one_mul, mul_comm, μ, h] using hGood
  have hg : h / 4 ≤ (μ {ω | GoodHole ω t R 0}).toReal := by linarith
  have hs := measure_holeCloser_ge_good hd (threePointLaw p) t R
  have hc := mul_le_mul_of_nonneg_right hg (pow_nonneg (by positivity : 0 ≤ ((R + 1 : ℕ) : ℝ)) d)
  calc h / 4 * ((R + 1 : ℕ) : ℝ) ^ d
    ≤ (μ {ω | GoodHole ω t R 0}).toReal * ((R + 1 : ℕ) : ℝ) ^ d := hc
    _ ≤ (μ {ω | HoleCloser ω t}).toReal := by simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hs

end Parking
