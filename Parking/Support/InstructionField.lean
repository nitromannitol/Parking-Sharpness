import Parking.Support.MatchedCounts

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Arriving table entries from an arbitrary active-count field. -/
def countArrivals (A : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool) (x : Site d) : Finset (RoundSlot d) :=
  (nbrFinset x).biUnion fun y =>
    ((Finset.range (A y)).filter fun j => y + stepVec (τ (Sum.inl (y, j))) = x).image
      fun j => Sum.inl (y, j)

/-- A used entry arrives precisely at the site its direction specifies. -/
theorem mem_countArrivals (A : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (x v : Site d) (j : ℕ) :
    Sum.inl (v, j) ∈ countArrivals A τ x ↔ j < A v ∧ v + stepVec (τ (Sum.inl (v, j))) = x := by
  classical
  simp only [countArrivals, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨y, _hy, k, ⟨hk, hx⟩, heq⟩
    cases Sum.inl_injective heq
    exact ⟨hk, hx⟩
  · rintro ⟨hj, hx⟩
    refine ⟨v, ?_, j, ⟨hj, hx⟩, rfl⟩
    rw [← hx]
    exact nbrFinset_symm (mem_nbrFinset_add_stepVec v _)

/-- The new signed field after a round. -/
def roundSigned (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool) (x : Site d) : ℤ :=
  (countArrivals A τ x).card - H x

/-- Suppressing a used instruction leaves a background independent of that instruction. -/
def roundWithout (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (v : Site d) (j : ℕ) (x : Site d) : ℤ :=
  ((countArrivals A τ x).erase (Sum.inl (v, j))).card - H x

/-- Reinserting the suppressed instruction adds exactly one particle at its destination. -/
theorem roundSigned_eq_addParticle (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (v : Site d) (j : ℕ) (hj : j < A v) :
    roundSigned A H τ = addParticle (v + stepVec (τ (Sum.inl (v, j)))) (roundWithout A H τ v j) := by
  classical
  ext x
  by_cases hx : x = v + stepVec (τ (Sum.inl (v, j)))
  · have hmem : Sum.inl (v, j) ∈ countArrivals A τ x := (mem_countArrivals _ _ _ _ _).mpr ⟨hj, hx.symm⟩
    have hc := Finset.card_erase_add_one hmem
    simp only [roundSigned, roundWithout, addParticle, if_pos hx]
    omega
  · have hn : Sum.inl (v, j) ∉ countArrivals A τ x := by
      rw [mem_countArrivals]
      exact fun h => hx h.2.symm
    simp only [roundSigned, roundWithout, addParticle, if_neg hx, Finset.erase_eq_of_notMem hn]

/-- Removing an entry removes all dependence on its value. -/
theorem roundWithout_update (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (v : Site d) (j : ℕ) (b : Fin d × Bool) :
    roundWithout A H (Function.update τ (Sum.inl (v, j)) b) v j = roundWithout A H τ v j := by
  classical
  ext x
  unfold roundWithout
  apply congrArg (fun s : Finset (RoundSlot d) => (s.card : ℤ) - H x)
  ext q
  cases q with
  | inr p => simp [countArrivals]
  | inl q =>
      rcases q with ⟨u, k⟩
      simp only [Finset.mem_erase, mem_countArrivals]
      constructor
      · rintro ⟨hne, hq, hx⟩
        exact ⟨hne, hq, by simpa only [Function.update_of_ne hne] using hx⟩
      · rintro ⟨hne, hq, hx⟩
        exact ⟨hne, hq, by simpa only [Function.update_of_ne hne] using hx⟩
end Parking
