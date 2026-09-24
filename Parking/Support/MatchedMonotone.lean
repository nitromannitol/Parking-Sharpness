import Parking.Support.InstructionField

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Increasing the outgoing counts includes every previously used arrival slot. -/
theorem countArrivals_mono (A B : Site d → ℕ) (hAB : ∀ y, A y ≤ B y)
    (τ : RoundSlot d → Fin d × Bool) (x : Site d) :
    countArrivals A τ x ⊆ countArrivals B τ x := by
  classical
  intro q hq
  obtain ⟨v, hv, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  apply Finset.mem_biUnion.mpr
  refine ⟨v, hv, Finset.mem_image.mpr ⟨j, ?_, rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    ((Finset.mem_range.mp (Finset.mem_filter.mp hj).1).trans_le (hAB v)),
    (Finset.mem_filter.mp hj).2⟩

/-- Common tables preserve the order of configurations in particle, hole, and odometer counts. -/
theorem matched_counts_mono (η ζ : Site d → ℤ) (hη : ∀ y, η y ≤ ζ y)
    (ρ ρ' : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) :
    (∀ x, matchedCount η ρ σ t x ≤ matchedCount ζ ρ' σ t x) ∧
    (∀ x, (matchedState ζ ρ' σ t).holes x ≤ (matchedState η ρ σ t).holes x) ∧
    (∀ x, (matchedState η ρ σ t).departures x ≤ (matchedState ζ ρ' σ t).departures x) := by
  induction t with
  | zero =>
      refine ⟨fun x => ?_, fun x => ?_, fun _ => le_rfl⟩
      · rw [matchedCount_zero, matchedCount_zero]
        exact Int.toNat_le_toNat (hη x)
      · change (-ζ x).toNat ≤ (-η x).toNat
        exact Int.toNat_le_toNat (neg_le_neg (hη x))
  | succ t ih =>
      have ha (x : Site d) : (matchedArrivals η ρ σ t x).card ≤
          (matchedArrivals ζ ρ' σ t x).card := by
        rw [card_matchedArrivals, card_matchedArrivals]
        exact Finset.card_le_card (countArrivals_mono _ _ ih.1 (σ t) x)
      refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
      · rw [matchedCount_succ, matchedCount_succ]
        have h₁ := ih.2.1 x
        have h₂ := ha x
        omega
      · rw [matchedHoles_succ, matchedHoles_succ]
        have h₁ := ih.2.1 x
        have h₂ := ha x
        omega
      · change (matchedState η ρ σ t).departures x + matchedCount η ρ σ t x ≤
          (matchedState ζ ρ' σ t).departures x + matchedCount ζ ρ' σ t x
        exact Nat.add_le_add (ih.2.2 x) (ih.1 x)
end Parking
