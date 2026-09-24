import Parking.Support.MatchedCounts
import Parking.Support.KernelBridge
import Parking.Support.MatchedUniform

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Agreement of used entries in the causal box suffices for agreement of the count process. -/
theorem matched_counts_agree_used_box (η η' : Site d → ℤ)
    (ρ ρ' : Label d × ℕ → ℝ) (σ σ' : RoundNoise d) (v : Site d) (t R : ℕ)
    (hη : ∀ y ∈ boxFinset v (R + t), η y = η' y)
    (hσ : ∀ s < t, ∀ y ∈ boxFinset v (R + t), ∀ j, j < matchedCount η ρ σ s y →
      σ s (Sum.inl (y, j)) = σ' s (Sum.inl (y, j))) :
    ∀ x ∈ boxFinset v R,
      matchedCount η ρ σ t x = matchedCount η' ρ' σ' t x ∧
      (matchedState η ρ σ t).holes x = (matchedState η' ρ' σ' t).holes x ∧
      (matchedState η ρ σ t).departures x = (matchedState η' ρ' σ' t).departures x := by
  induction t generalizing R with
  | zero =>
      intro x hx
      have he := hη x (by simpa using hx)
      simp only [matchedCount_zero, matchedState, initial, he, and_self]
  | succ t ih =>
      have hrt : R + 1 + t = R + (t + 1) := by omega
      have hp := ih (R + 1) (fun y hy => hη y (by rwa [← hrt]))
        (fun s hs y hy j hj => hσ s (by omega) y (by rwa [← hrt]) j hj)
      intro x hx
      have hx' : x ∈ boxFinset v (R + 1) := boxFinset_mono (by omega) hx
      have hn (y : Site d) (hy : y ∈ nbrFinset x) : y ∈ boxFinset v (R + 1) := by
        have h := mem_boxFinset_add hx (nbrFinset_subset_box x hy)
        simpa only [Nat.add_comm 1 R] using h
      have ha : (matchedArrivals η ρ σ t x).card = (matchedArrivals η' ρ' σ' t x).card := by
        rw [card_matchedArrivals, card_matchedArrivals]
        unfold arrivalSlots
        congr 1
        apply Finset.biUnion_congr rfl
        intro y hy
        rw [(hp y (hn y hy)).1]
        congr 1
        apply Finset.filter_congr
        intro j hj
        have hj' : j < matchedCount η ρ σ t y := by
          rw [(hp y (hn y hy)).1]
          exact Finset.mem_range.mp hj
        rw [hσ t (by omega) y (boxFinset_mono (by omega) (hn y hy)) j hj']
      refine ⟨?_, ?_, ?_⟩
      · rw [matchedCount_succ, matchedCount_succ, ha, (hp x hx').2.1]
      · rw [matchedHoles_succ, matchedHoles_succ, ha, (hp x hx').2.1]
      · change (matchedState η ρ σ t).departures x + matchedCount η ρ σ t x =
          (matchedState η' ρ' σ' t).departures x + matchedCount η' ρ' σ' t x
        rw [(hp x hx').1, (hp x hx').2.2]
/-- Bounded initial counts reduce the relevant instruction table to finitely many ranks. -/
theorem matched_counts_agree_finite_noise (η η' : Site d → ℤ)
    (K : ℕ) (hK : ∀ y, (η y).toNat ≤ K)
    (ρ ρ' : Label d × ℕ → ℝ) (σ σ' : RoundNoise d) (v : Site d) (t R : ℕ)
    (hη : ∀ y ∈ boxFinset v (R + t), η y = η' y)
    (hσ : ∀ s < t, ∀ y ∈ boxFinset v (R + t), ∀ j < (2 * t + 1) ^ d * K,
      σ s (Sum.inl (y, j)) = σ' s (Sum.inl (y, j))) :
    ∀ x ∈ boxFinset v R,
      matchedCount η ρ σ t x = matchedCount η' ρ' σ' t x ∧
      (matchedState η ρ σ t).holes x = (matchedState η' ρ' σ' t).holes x ∧
      (matchedState η ρ σ t).departures x = (matchedState η' ρ' σ' t).departures x := by
  apply matched_counts_agree_used_box η η' ρ ρ' σ σ' v t R hη
  intro s hs y hy j hj
  apply hσ s hs y hy j
  apply hj.trans_le
  apply (matchedCount_le_box η K hK ρ σ s y).trans
  exact Nat.mul_le_mul_right K (Nat.pow_le_pow_left (by omega) d)
end Parking
