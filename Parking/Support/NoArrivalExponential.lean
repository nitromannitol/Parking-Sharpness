import Parking.Support.NoArrivalWeight
import Parking.Support.LayerReward

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The no-arrival exponential supermartingale starts at one and has expectation at most one. -/
theorem integral_noArrivalWeight_le_one (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    ∫ σ, noArrivalWeight η ρ σ T x ∂(roundNoiseLaw d) ≤ 1 := by
  haveI := stepLaw_isProbability hd
  haveI := roundNoiseLaw_isProbability hd
  let Q := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  induction T with
  | zero => simp only [noArrivalWeight_zero, integral_const, probReal_univ, one_smul, le_refl]
  | succ T ih =>
      apply le_trans _ ih
      exact integral_le_of_bounded_layer_sections Q
        (fun σ => noArrivalWeight η ρ σ (T + 1) x) (fun σ => noArrivalWeight η ρ σ T x)
        (measurable_noArrivalWeight hd η ρ (T + 1) x) (measurable_noArrivalWeight hd η ρ T x)
        _ _ (fun σ => noArrivalWeight_bound hd η K hη ρ σ (T + 1) x)
        (fun σ => noArrivalWeight_bound hd η K hη ρ σ T x) T
        (fun σ => noArrivalWeight_section hd η ρ σ T x)
end Parking
