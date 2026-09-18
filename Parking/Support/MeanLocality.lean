import Parking.Support.MatchedLocality
import Parking.Support.SingleMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A finite-horizon conditional mean reads only a finite box of the initial field. -/
theorem matchedMeanU_agree_box (η η' : Site d → ℤ) (ρ ρ' : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (hη : ∀ y ∈ boxFinset x T, η y = η' y) :
    matchedMeanU η ρ T x = matchedMeanU η' ρ' T x := by
  apply integral_congr_ae
  apply ae_of_all
  intro σ
  have h := matched_counts_agree_box η η' ρ ρ' σ σ x T 0 (by simpa using hη)
    (fun _ _ _ _ _ => rfl) x (mem_boxFinset_iff.mpr fun _ => by simp)
  exact congrArg (fun k : ℕ => (k : ℝ)) h.2.2

/-- An added particle beyond the finite propagation box has zero influence. -/
theorem matchedMeanU_addParticle_of_far (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x v : Site d) (hv : v ∉ boxFinset x T) :
    matchedMeanU (addParticle v η) ρ T x = matchedMeanU η ρ T x := by
  apply matchedMeanU_agree_box
  intro y hy
  have hne : y ≠ v := fun he => hv (he ▸ hy)
  simp only [addParticle, if_neg hne]
end Parking
