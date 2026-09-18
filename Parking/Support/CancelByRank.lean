/-
Pairing opposite finite lists by priority. Every cancelled label has a unique
partner; cancellation preserves the signed count and leaves at most one sign.
-/
import LatticeProb.Rank

noncomputable section

open LatticeProb

variable {α β : Type*} [DecidableEq α] [LinearOrder β]

/-- Opposite lists are paired in increasing priority order; elements of the
first list whose rank exceeds the size of the second list survive. -/
def Parking.rankSurvivors (A B : Finset α) (f : α → β) : Finset α :=
  A.filter fun p => B.card ≤ rankIn A f p

/-- Two labels are cancelled together when their ranks in the opposite lists agree. -/
def Parking.RankPair (A B : Finset α) (f : α → β) (p q : α) : Prop :=
  p ∈ A ∧ q ∈ B ∧ rankIn A f p = rankIn B f q

omit [DecidableEq α] in
theorem Parking.rankSurvivors_subset (A B : Finset α) (f : α → β) :
    Parking.rankSurvivors A B f ⊆ A := Finset.filter_subset _ _

theorem Parking.card_rankSurvivors (A B : Finset α) (f : α → β) (hf : Set.InjOn f A) :
    (Parking.rankSurvivors A B f).card = A.card - B.card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := A) (p := fun p => rankIn A f p < B.card)
  have hc := LatticeProb.card_filter_rank_lt A f hf B.card
  change (A.filter fun p => rankIn A f p < B.card).card = min A.card B.card at hc
  simp only [not_lt] at h
  change _ + (Parking.rankSurvivors A B f).card = _ at h
  omega

omit [DecidableEq α] in
theorem Parking.rankPair_symm {A B : Finset α} {f : α → β} {p q : α}
    (hpq : Parking.RankPair A B f p q) : Parking.RankPair B A f q p :=
  ⟨hpq.2.1, hpq.1, hpq.2.2.symm⟩

/-- A cancelled label has exactly one opposite partner. -/
theorem Parking.existsUnique_rankPair (A B : Finset α) (f : α → β)
    (hfB : Set.InjOn f B) {p : α} (hp : p ∈ A)
    (hdead : p ∉ Parking.rankSurvivors A B f) :
    ∃! q, Parking.RankPair A B f p q := by
  have hr : rankIn A f p < B.card := by
    simpa [Parking.rankSurvivors, hp] using hdead
  have hm : rankIn A f p ∈ B.image (rankIn B f) := by
    rw [image_rankIn hfB]
    exact Finset.mem_range.mpr hr
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hm
  refine ⟨q, ⟨hp, hq, heq.symm⟩, fun q' hq' => ?_⟩
  exact rankIn_injOn hfB hq'.2.1 hq (hq'.2.2.symm.trans heq.symm)

theorem Parking.not_mem_rankSurvivors_of_pair {A B : Finset α} {f : α → β} {p q : α}
    (hpq : Parking.RankPair A B f p q) : p ∉ Parking.rankSurvivors A B f := by
  intro hp
  have hle := (Finset.mem_filter.mp hp).2
  rw [hpq.2.2] at hle
  exact (not_lt_of_ge hle) (rankIn_lt_card hpq.2.1)

/-- Cancelling equal-priority ranks preserves the signed number of labels. -/
theorem Parking.signed_card_rankSurvivors (A B : Finset α) (f : α → β)
    (hfA : Set.InjOn f A) (hfB : Set.InjOn f B) :
    ((Parking.rankSurvivors A B f).card : ℤ) - (Parking.rankSurvivors B A f).card =
      (A.card : ℤ) - B.card := by
  rw [Parking.card_rankSurvivors A B f hfA, Parking.card_rankSurvivors B A f hfB]
  omega

/-- After cancellation, at most one sign remains. -/
theorem Parking.rankSurvivors_empty_or_empty (A B : Finset α) (f : α → β)
    (hfA : Set.InjOn f A) (hfB : Set.InjOn f B) :
    Parking.rankSurvivors A B f = ∅ ∨ Parking.rankSurvivors B A f = ∅ := by
  rw [← Finset.card_eq_zero, ← Finset.card_eq_zero,
    Parking.card_rankSurvivors A B f hfA, Parking.card_rankSurvivors B A f hfB]
  omega

end
