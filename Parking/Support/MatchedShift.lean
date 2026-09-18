/-
Translation covariance of particle rounds and the coupled common-table
construction, including the priority ranks and auxiliary noise entries.
-/
import Parking.Support.Matched
import Parking.Support.Equivariance

noncomputable section

open LatticeProb

variable {d : ℕ}

/-- Translation of the particle-driven data. -/
structure Parking.PShiftDriver (v : Site d) (D' D : Parking.PDriver d) : Prop where
  eta : ∀ x, D'.eta x = D.eta (x + v)
  move : ∀ p t, D'.move (p, t) = D.move (Parking.shiftLabel v p, t)
  rank : ∀ p t, D'.rank (p, t) = D.rank (Parking.shiftLabel v p, t)

variable {v : Site d} {D' D : Parking.PDriver d} {S' S : State d}

/-- Translation preserves comparisons of the complete priority keys. -/
theorem Parking.matchKey_shift_lt (v : Site d) (ρ : Label d × ℕ → ℝ)
    (t : ℕ) (p q : Label d) :
    Parking.matchKey (Parking.shiftRank v ρ) t p < Parking.matchKey (Parking.shiftRank v ρ) t q ↔
      Parking.matchKey ρ t (Parking.shiftLabel v p) < Parking.matchKey ρ t (Parking.shiftLabel v q) := by
  simp only [Parking.matchKey, Prod.Lex.toLex_lt_toLex, Parking.shiftRank]
  rw [show labelKey (Parking.shiftLabel v p) < labelKey (Parking.shiftLabel v q) ↔
    labelKey p < labelKey q from Parking.labelLT_shift v p q]

/-- Ranks transport along translated finite sets. -/
theorem Parking.rankIn_shift (v : Site d) (ρ : Label d × ℕ → ℝ) (t : ℕ)
    (A' A : Finset (Label d)) (hA : A'.map (Parking.shiftLabelEmb v) = A) (p : Label d) :
    rankIn A' (Parking.matchKey (Parking.shiftRank v ρ) t) p =
      rankIn A (Parking.matchKey ρ t) (Parking.shiftLabel v p) := by
  classical
  unfold rankIn
  rw [← hA, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro q _
  exact Parking.matchKey_shift_lt v ρ t q p

theorem Parking.matchActive_shift (η : Site d → ℤ) (hS : Parking.ShiftState v S' S)
    (t : ℕ) (x : Site d) :
    (Parking.matchActive (fun y => η (y + v)) S' t x).map (Parking.shiftLabelEmb v) =
      Parking.matchActive η S t (x + v) := by
  classical
  unfold Parking.matchActive
  rw [← Parking.candidates_shift η x v t, Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [Function.comp_def, Parking.shiftLabelEmb_apply, hS.active, hS.pos,
    sub_eq_iff_eq_add]

theorem Parking.pActiveAt_shift (hD : Parking.PShiftDriver v D' D)
    (hS : Parking.ShiftState v S' S) (t : ℕ) (x : Site d) :
    (Parking.pActiveAt D' S' t x).map (Parking.shiftLabelEmb v) =
      Parking.pActiveAt D S t (x + v) := by
  change (Parking.matchActive D'.eta S' t x).map _ = Parking.matchActive D.eta S t (x + v)
  rw [show D'.eta = fun y => D.eta (y + v) from funext hD.eta]
  exact Parking.matchActive_shift D.eta hS t x

theorem Parking.pNextPos_shift (hD : Parking.PShiftDriver v D' D)
    (hS : Parking.ShiftState v S' S) (t : ℕ) (p : Label d) :
    Parking.pNextPos D' S' t p = Parking.pNextPos D S t (Parking.shiftLabel v p) - v := by
  simp only [Parking.pNextPos, hS.active, hS.pos, hD.move]
  split <;> abel

theorem Parking.pArrivalsAt_shift (hD : Parking.PShiftDriver v D' D)
    (hS : Parking.ShiftState v S' S) (t : ℕ) (x : Site d) :
    (Parking.pArrivalsAt D' S' t x).map (Parking.shiftLabelEmb v) =
      Parking.pArrivalsAt D S t (x + v) := by
  classical
  unfold Parking.pArrivalsAt
  rw [show D'.eta = fun y => D.eta (y + v) from funext hD.eta,
    ← Parking.candidates_shift D.eta x v (t + 1), Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [Function.comp_def, Parking.shiftLabelEmb_apply, hS.active,
    Parking.pNextPos_shift hD hS, sub_eq_iff_eq_add]

theorem Parking.pSettles_shift (hD : Parking.PShiftDriver v D' D)
    (hS : Parking.ShiftState v S' S) (t : ℕ) (p : Label d) :
    Parking.pSettles D' S' t p = Parking.pSettles D S t (Parking.shiftLabel v p) := by
  classical
  have hr : D'.rank = Parking.shiftRank v D.rank := by
    funext q
    exact hD.rank q.1 q.2
  have hcard := Parking.rankIn_shift v D.rank t _ _
    (Parking.pArrivalsAt_shift hD hS t (Parking.pNextPos D' S' t p)) p
  rw [Parking.pNextPos_shift hD hS, sub_add_cancel] at hcard
  have hhole : S'.holes (Parking.pNextPos D' S' t p) =
      S.holes (Parking.pNextPos D S t (Parking.shiftLabel v p)) := by
    rw [hS.holes, Parking.pNextPos_shift hD hS, sub_add_cancel]
  simp only [rankIn, Parking.matchKey, Prod.Lex.toLex_lt_toLex, ← hr] at hcard
  unfold Parking.pSettles
  rw [hS.active, hhole]
  simp only [labelLT, Parking.pNextPos_shift hD hS, hcard]

theorem Parking.pStep_shift (hD : Parking.PShiftDriver v D' D)
    (hS : Parking.ShiftState v S' S) (t : ℕ) :
    Parking.ShiftState v (Parking.pStep D' S' t) (Parking.pStep D S t) where
  active p := by simp only [Parking.pStep, hS.active, Parking.pSettles_shift hD hS]
  pos p := Parking.pNextPos_shift hD hS t p
  holes x := by
    simp only [Parking.pStep, hS.holes]
    rw [← Parking.pArrivalsAt_shift hD hS, Finset.card_map]
  departures x := by
    simp only [Parking.pStep, hS.departures]
    rw [← Parking.pActiveAt_shift hD hS, Finset.card_map]

/-- Membership transports along a translated finite set. -/
theorem Parking.mem_finset_shift (v : Site d) (A' A : Finset (Label d))
    (hA : A'.map (Parking.shiftLabelEmb v) = A) (p : Label d) :
    p ∈ A' ↔ Parking.shiftLabel v p ∈ A := by
  rw [← hA]
  constructor
  · intro hp
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
  · intro hp
    obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hp
    exact (Parking.shiftLabel_injective v he) ▸ hq

/-- Translation of a common-table entry. -/
def Parking.shiftRoundSlot (v : Site d) : Parking.RoundSlot d → Parking.RoundSlot d
  | Sum.inl (x, j) => Sum.inl (x + v, j)
  | Sum.inr p => Sum.inr (Parking.shiftLabel v p)

theorem Parking.shiftRoundSlot_injective (v : Site d) :
    Function.Injective (Parking.shiftRoundSlot v) := by
  intro p q h
  cases p with
  | inl p =>
      cases q with
      | inl q =>
          have he := Sum.inl_injective h
          have hx : p.1 = q.1 := add_right_cancel (congrArg (fun z : Site d × ℕ => z.1) he)
          have hi := congrArg (fun z : Site d × ℕ => z.2) he
          exact congrArg Sum.inl (Prod.ext hx hi)
      | inr q => cases h
  | inr p =>
      cases q with
      | inl q => cases h
      | inr q => exact congrArg Sum.inr (Parking.shiftLabel_injective v (Sum.inr_injective h))

def Parking.shiftRoundNoise (v : Site d) (σ : Parking.RoundNoise d) : Parking.RoundNoise d :=
  fun t q => σ t (Parking.shiftRoundSlot v q)

/-- Matching uses the translated table entry after translating a state. -/
theorem Parking.matchSlot_shift (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (hS : Parking.ShiftState v S' S) (t : ℕ) (p : Label d) :
    Parking.shiftRoundSlot v
      (Parking.matchSlot (fun y => η (y + v)) (Parking.shiftRank v ρ) S' t p) =
      Parking.matchSlot η ρ S t (Parking.shiftLabel v p) := by
  classical
  have hA : (Parking.matchActive (fun y => η (y + v)) S' t (S'.pos p)).map
      (Parking.shiftLabelEmb v) = Parking.matchActive η S t (S.pos (Parking.shiftLabel v p)) := by
    simpa only [hS.pos, sub_add_cancel] using Parking.matchActive_shift η hS t (S'.pos p)
  have hm := Parking.mem_finset_shift v _ _ hA p
  have hr := Parking.rankIn_shift v ρ t _ _ hA p
  unfold Parking.matchSlot
  by_cases hp : p ∈ Parking.matchActive (fun y => η (y + v)) S' t (S'.pos p)
  · rw [if_pos hp, if_pos (hm.mp hp)]
    change Sum.inl (S'.pos p + v, _) = Sum.inl _
    rw [hr, hS.pos, sub_add_cancel]
  · rw [if_neg hp, if_neg (fun h => hp (hm.mpr h))]
    rfl

/-- The common-table physical dynamics commute with translations. -/
theorem Parking.matchedState_shift (v : Site d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) :
    Parking.ShiftState v
      (Parking.matchedState (fun y => η (y + v)) (Parking.shiftRank v ρ)
        (Parking.shiftRoundNoise v σ) t)
      (Parking.matchedState η ρ σ t) := by
  induction t with
  | zero =>
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun _ => rfl⟩
      · rfl
      · simp only [Parking.matchedState, initial, Parking.shiftLabel]
        abel
      · rfl
  | succ t ih =>
      apply Parking.pStep_shift _ ih
      refine ⟨fun _ => rfl, ?_, fun _ _ => rfl⟩
      intro p k
      change σ k (Parking.shiftRoundSlot v
        (Parking.matchSlot _ _ _ k p)) = σ k (Parking.matchSlot _ _ _ k (Parking.shiftLabel v p))
      rw [Parking.matchSlot_shift η ρ ih]

end
