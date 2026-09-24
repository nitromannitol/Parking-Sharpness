import Parking.Support.HoleSinkEvent
import Parking.Support.TableHoleLaw
import Parking.Support.NoArrivalJoint
import Parking.Support.ClosePair
import LatticeProb.Prob.Coordinate

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The sparse hole probability is p times the probability of no entrance to the sink. -/
theorem holeProb_eq_mul_sink_noArrival (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (T : ℕ) :
    holeProb d (threePointLaw p) T = p *
      (((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d))
        {z | noArrivalFlag (sparseSinkField T 0 z.1) 0 (curryRoundNoise z.2) T 0 = true}).toReal := by
  classical
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  let μ := (iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)
  let G : Set ((Site d → ℤ) × FlatRoundNoise d) :=
    {z | noArrivalFlag (sparseSinkField T 0 z.1) 0 (curryRoundNoise z.2) T 0 = true}
  let F := G.indicator (fun _ => (1 : ℝ))
  let Hset : Set ((Site d → ℤ) × FlatRoundNoise d) :=
    {z | (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) T).holes 0 = 1}
  have hG : MeasurableSet G := (measurable_noArrivalFlag_of hd _ _ _
    ((measurable_sparseSinkField T 0).comp measurable_fst) measurable_const
    (measurable_curryRoundNoise.comp measurable_snd) T 0) (measurableSet_singleton true)
  have hH : MeasurableSet Hset := (measurable_clippedTableHole hd T 0) (measurableSet_singleton 1)
  have hF : Measurable F := measurable_const.indicator hG
  have hiF : Integrable F μ := (integrable_const _).indicator hG
  have hinv (η : Site d → ℤ) (ξ : FlatRoundNoise d) : F (Function.update η 0 0, ξ) = F (η, ξ) := by
    have he : (Function.update η 0 0, ξ) ∈ G ↔ (η, ξ) ∈ G := by
      dsimp only [G, Set.mem_setOf_eq]
      rw [sparseSinkField_update]
    dsimp only [F]
    by_cases hg : (η, ξ) ∈ G
    · rw [Set.indicator_of_mem (he.mpr hg), Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem (fun h => hg (he.mp h)), Set.indicator_of_notMem hg]
  have hfactor := integral_mul_indicator_eval_prod (μ := fun _ : Site d => threePointLaw p)
    (flatRoundNoiseLaw d) (0 : Site d) (0 : ℤ) F hF hiF hinv (measurableSet_singleton (-1 : ℤ))
  have hae : ∀ᵐ z ∂μ, clippedField z.1 = z.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (ae_clippedField (threePointLaw p) (ae_clipSparse_threePointLaw p))
  have he : (∫ z, Hset.indicator (fun _ => (1 : ℝ)) z ∂μ) =
      ∫ z, F z * Set.indicator ({-1} : Set ℤ) (fun _ => (1 : ℝ)) (z.1 0) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with z hz
    have hmem : z ∈ Hset ↔ z.1 0 = -1 ∧ z ∈ G := by
      change (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) T).holes 0 = 1 ↔ _
      rw [clippedHole_eq_one_iff_sink]
      rw [hz]
      rfl
    by_cases hη : z.1 0 = -1 <;> by_cases hg : z ∈ G <;>
      simp [F, Set.indicator_of_mem, Set.indicator_of_notMem, hmem, hη, hg]
  change (∫ z, F z * Set.indicator ({-1} : Set ℤ) (fun _ => (1 : ℝ)) (z.1 0) ∂μ) =
    ((threePointLaw p) {-1}).toReal * ∫ z, F z ∂μ at hfactor
  rw [hfactor] at he
  dsimp only [F] at he
  rw [integral_indicator_const (1 : ℝ) hH, integral_indicator_const (1 : ℝ) hG,
    threePointLaw_singleton_neg, ENNReal.toReal_ofReal hp.le] at he
  simp only [smul_eq_mul, mul_one] at he
  rw [holeProb_eq_clippedTable hd _ (ae_clipSparse_threePointLaw p) T]
  exact he
end Parking
