import Parking.Support.HoleSinkLaw
import Parking.Support.HolePositive

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Hole counts decrease at every round in the common-table process. -/
theorem matchedHoles_antitone (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (v : Site d) : Antitone (fun t => (matchedState η ρ σ t).holes v) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [matchedHoles_succ]
  exact Nat.sub_le _ _

/-- The sparse surviving-hole probability decreases with time. -/
theorem holeProb_antitone (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) :
    Antitone (holeProb d (threePointLaw p)) := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  intro s t hst
  rw [holeProb_eq_clippedTable hd _ (ae_clipSparse_threePointLaw p) t,
    holeProb_eq_clippedTable hd _ (ae_clipSparse_threePointLaw p) s]
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono _)
  intro z hz
  have hmono := matchedHoles_antitone (clippedField z.1) 0 (curryRoundNoise z.2) 0 hst
  change (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) t).holes 0 ≤
    (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) s).holes 0 at hmono
  have hi := matchedHoles_le_initial (clippedField z.1) 0 (curryRoundNoise z.2) s 0
  have hc : -1 ≤ clippedField z.1 0 := (clipSparse_bounds (z.1 0)).1
  change (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) t).holes 0 = 1 at hz
  change (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) s).holes 0 = 1
  omega

/-- A hole can survive only when its initial site was a hole. -/
theorem holeProb_le_p (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (T : ℕ) :
    holeProb d (threePointLaw p) T ≤ p := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  rw [holeProb_eq_mul_sink_noArrival hd hp hp4 T]
  apply mul_le_of_le_one_right hp.le
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq (by simp)
end Parking
