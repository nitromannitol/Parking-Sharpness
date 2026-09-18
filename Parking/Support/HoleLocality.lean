import Parking.Support.MatchedLocality
import Parking.Support.HoleMean
import Parking.Support.RoundMeanField

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A finite-horizon conditional hole mean reads only a finite box of the initial field. -/
theorem matchedMeanH_agree_box (η η' : Site d → ℤ) (ρ ρ' : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (hη : ∀ y ∈ boxFinset x T, η y = η' y) :
    matchedMeanH η ρ T x = matchedMeanH η' ρ' T x := by
  apply integral_congr_ae
  apply ae_of_all
  intro σ
  have h := matched_counts_agree_box η η' ρ ρ' σ σ x T 0 (by simpa using hη)
    (fun _ _ _ _ _ => rfl) x (mem_boxFinset_iff.mpr fun _ => by simp)
  exact congrArg (fun k : ℕ => (k : ℝ)) h.2.1

/-- An added particle beyond the finite propagation box has zero influence. -/
theorem matchedMeanH_addParticle_of_far (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x v : Site d) (hv : v ∉ boxFinset x T) :
    matchedMeanH (addParticle v η) ρ T x = matchedMeanH η ρ T x := by
  apply matchedMeanH_agree_box
  intro y hy
  have hne : y ≠ v := fun he => hv (he ▸ hy)
  simp only [addParticle, if_neg hne]

/-- Only finitely many potentially used entries can affect the future mean at a site. -/
theorem roundMeanH_agree_finite (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (τ τ' : RoundSlot d → Fin d × Bool)
    (hτ : ∀ y ∈ boxFinset x (T + 1), ∀ j < N, τ (Sum.inl (y, j)) = τ' (Sum.inl (y, j))) :
    matchedMeanH (roundSigned A H τ) ρ T x = matchedMeanH (roundSigned A H τ') ρ T x := by
  classical
  apply matchedMeanH_agree_box
  intro y hy
  unfold roundSigned
  apply congrArg (fun s : Finset (RoundSlot d) => (s.card : ℤ) - H y)
  apply Finset.biUnion_congr rfl
  intro z hz
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hzx : z ∈ boxFinset x (T + 1) := by
    simpa only [Nat.add_comm 1 T] using mem_boxFinset_add hy (nbrFinset_subset_box y hz)
  rw [hτ z hzx j ((Finset.mem_range.mp hj).trans_le (hA z))]
end Parking
