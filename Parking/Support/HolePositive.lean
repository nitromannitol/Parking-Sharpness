import Parking.Support.TableHoleLaw
import Parking.Support.HoleNoArrival
import Parking.Support.HorizonSink
import Parking.Support.AtomUpdate
import Parking.Support.ClosePair

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A field consisting entirely of single holes keeps all of its holes. -/
theorem matchedHole_const_neg_one (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    (matchedState (fun _ => -1) ρ σ T).holes x = 1 := by
  apply (matchedHole_eq_one_iff_noArrival _ x rfl ρ σ T).mpr
  apply (noArrivalFlag_iff _ _ _ _ _).mpr
  intro s _
  have h := matchedArrivals_le_box (fun _ : Site d => -1) 0 (by intro y; norm_num) ρ σ s x
  simpa only [mul_zero, Nat.le_zero] using h

/-- Prescribing single holes in the causal box guarantees survival at its center. -/
theorem clippedHole_overwrite_box (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T : ℕ) (v : Site d) :
    (matchedState (clippedField (fun y => if y ∈ boxFinset v T then -1 else η y)) ρ σ T).holes v = 1 := by
  classical
  have h := matched_counts_agree_box
    (clippedField (fun y => if y ∈ boxFinset v T then -1 else η y)) (fun _ => -1)
    ρ ρ σ σ v T 0
    (fun y hy => by simp only [zero_add] at hy; simp [clippedField, hy, clipSparse])
    (fun _ _ _ _ _ => rfl) v (by simp [mem_boxFinset_iff])
  exact h.2.1.trans (matchedHole_const_neg_one ρ σ T v)

/-- Every finite-horizon sparse hole probability is strictly positive. -/
theorem holeProb_pos (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (T : ℕ) :
    0 < holeProb d (threePointLaw p) T := by
  classical
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  rw [holeProb_eq_clippedTable hd _ (ae_clipSparse_threePointLaw p) T]
  apply ENNReal.toReal_pos
  · by_contra hz
    have hbad : ∀ᵐ z ∂((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)),
        (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) T).holes 0 ≠ 1 := by
      simpa only [ae_iff, not_not] using hz
    have hfield := Measure.ae_ae_of_ae_prod hbad
    have ha : threePointLaw p {-1} ≠ 0 := by
      rw [threePointLaw_singleton_neg]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
    have hf := ae_overwrite_infinitePi_atoms (threePointLaw p) (boxFinset (0 : Site d) T)
      (fun _ => (-1 : ℤ)) (fun _ _ => ha) hfield
    obtain ⟨η, hη⟩ := hf.exists
    obtain ⟨ξ, hξ⟩ := hη.exists
    exact hξ (clippedHole_overwrite_box η 0 (curryRoundNoise ξ) T 0)
  · exact measure_ne_top _ _
end Parking
