import Parking.Support.SafeTransport
import Parking.Support.FiniteTransport
import Parking.Support.IndicatorIntegral

/-!
# A density bound between good holes and hole closers

`measure_holeCloser_ge_good` compares the probabilities of two events built from the
same "safe mass" function `goodSafeMass`: on `GoodHole ω t R 0`, at least `(R + 1) ^ d`
sites of the box around the origin are safe, while every safe site itself contributes to
`HoleCloser ω t`. Translation-invariance of the safe-mass function
(`integral_box_transport`) lets the box sum bounding `GoodHole`'s indicator from below be
compared directly to the sum bounding `HoleCloser`'s indicator from above, giving the
stated inequality between their probabilities.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

/-- On `GoodHole`, at least `(R + 1) ^ d` sites are safe, and translation-invariance of
`goodSafeMass` (`integral_box_transport`) transfers this mass to bound the probability of
`HoleCloser` below by `(R + 1) ^ d` times the probability of `GoodHole`. -/
theorem measure_holeCloser_ge_good (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (t R : ℕ) :
    ((R + 1) ^ d : ℝ) * ((law d ν) {ω | GoodHole ω t R 0}).toReal ≤
      ((law d ν) {ω | HoleCloser ω t}).toReal := by
  haveI := stackRankLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((iidLaw d ν).prod (stackRankLaw d)))
  let μ := law d ν
  let F := fun (ω : Data d) (y w : Site d) => (goodSafeMass ω t R y w : ℝ)
  have hiF : ∀ y w, Integrable (fun ω => F ω y w) μ := by
    intro y w
    apply integrable_of_le_nat (measurable_goodSafeMass t R y w) (integrable_const 1)
    intro ω
    exact_mod_cast goodSafeMass_le_one ω t R y w
  have htrans := integral_box_transport hd ν F R hiF (fun v ω y w => by
    dsimp only [F]
    rw [goodSafeMass_shift])
  have hmC := measurableSet_HoleCloser (d := d) t
  have hiC := integrable_ite_one_zero μ _ hmC
  have hIn : (∫ ω, ∑ y ∈ boxFinset 0 R, F ω y 0 ∂μ) ≤ (μ {ω | HoleCloser ω t}).toReal := by
    rw [← integral_ite_one_zero μ _ hmC]
    apply integral_mono (integrable_finsetSum _ (fun y _ => hiF y 0)) hiC
    intro ω
    have h := goodSafeMass_in hd ω t R
    have hc := (Nat.cast_le (α := ℝ)).mpr h
    simpa only [F, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hc
  have hmG := measurableSet_GoodHole (d := d) t R 0
  have hiG := integrable_ite_one_zero μ _ hmG
  have hOut : ((R + 1) ^ d : ℝ) * (μ {ω | GoodHole ω t R 0}).toReal ≤
      ∫ ω, ∑ w ∈ boxFinset 0 R, F ω 0 w ∂μ := by
    rw [← integral_ite_one_zero μ _ hmG, ← integral_const_mul]
    apply integral_mono (hiG.const_mul _) (integrable_finsetSum _ (fun w _ => hiF 0 w))
    intro ω
    have hout : (∑ w ∈ boxFinset 0 R, F ω 0 w) =
        if GoodHole ω t R 0 then ((safeSites ω t R 0).card : ℝ) else 0 := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) (goodSafeMass_out ω t R)
      simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using h
    change ((R + 1) ^ d : ℝ) * (if GoodHole ω t R 0 then 1 else 0) ≤ ∑ w ∈ boxFinset 0 R, F ω 0 w
    rw [hout]
    by_cases h : GoodHole ω t R 0
    · simp only [h, if_true, mul_one]
      exact_mod_cast card_safeSites_lower h.2
    · simp only [h, if_false, mul_zero, le_refl]
  exact hOut.trans (htrans ▸ hIn)

end Parking
