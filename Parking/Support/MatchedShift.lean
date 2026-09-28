import Parking.Support.Matched
import Parking.Support.Equivariance

/-!
# Translation covariance of the common-table construction

Translation covariance of particle rounds and the coupled common-table construction,
including the priority ranks and auxiliary noise entries. Each stage of the particle-driven
dynamics (candidate sets, ranks, active labels, next positions, arrivals, settling and the
resulting state) is shown to commute with a shift `v` of the site lattice, once the driver
data (initial field, moves and ranks) and the common-table noise are shifted correspondingly.
-/

noncomputable section

open LatticeProb

variable {d : ℕ}

/-- Translation of the particle-driven data. -/
structure Parking.PShiftDriver (v : Site d) (D' D : Parking.PDriver d) : Prop where
  eta : ∀ x, D'.eta x = D.eta (x + v)
  move : ∀ p t, D'.move (p, t) = D.move (LatticeProb.shiftLabel v p, t)
  rank : ∀ p t, D'.rank (p, t) = D.rank (LatticeProb.shiftLabel v p, t)

variable {v : Site d} {D' D : Parking.PDriver d} {S' S : State d}

/-- Translation preserves comparisons of the complete priority keys. -/
theorem Parking.matchKey_shift_lt (v : Site d) (ρ : Label d × ℕ → ℝ)
    (t : ℕ) (p q : Label d) :
    Parking.matchKey (LatticeProb.shiftRank v ρ) t p <
        Parking.matchKey (LatticeProb.shiftRank v ρ) t q ↔
      Parking.matchKey ρ t (LatticeProb.shiftLabel v p) <
          Parking.matchKey ρ t (LatticeProb.shiftLabel v q) := by
  simp only [Parking.matchKey, Prod.Lex.toLex_lt_toLex, LatticeProb.shiftRank]
  rw [show labelKey (LatticeProb.shiftLabel v p) < labelKey (LatticeProb.shiftLabel v q) ↔
    labelKey p < labelKey q from LatticeProb.labelLT_shift v p q]

/-- Ranks transport along translated finite sets. -/
theorem Parking.rankIn_shift (v : Site d) (ρ : Label d × ℕ → ℝ) (t : ℕ)
    (A' A : Finset (Label d)) (hA : A'.map (LatticeProb.shiftLabelEmb v) = A) (p : Label d) :
    rankIn A' (Parking.matchKey (LatticeProb.shiftRank v ρ) t) p =
      rankIn A (Parking.matchKey ρ t) (LatticeProb.shiftLabel v p) := by
  classical
  unfold rankIn
  rw [← hA, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro q _
  exact Parking.matchKey_shift_lt v ρ t q p

/-- The active labels at a translated site, computed from the field shifted by `-v` and a
shifted state, are the image under the shift embedding of the active labels at the original
site: this follows from `candidates_shift` after rewriting the filter predicate along
`hS.active` and `hS.pos`. -/
theorem Parking.matchActive_shift (η : Site d → ℤ) (hS : LatticeProb.ShiftState v S' S)
    (t : ℕ) (x : Site d) :
    (Parking.matchActive (fun y => η (y + v)) S' t x).map (LatticeProb.shiftLabelEmb v) =
      Parking.matchActive η S t (x + v) := by
  classical
  unfold Parking.matchActive
  rw [← LatticeProb.candidates_shift η x v t, Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [Function.comp_def, LatticeProb.shiftLabelEmb_apply, hS.active, hS.pos,
    sub_eq_iff_eq_add]

/-- The particle-driven active labels transport the same way as `matchActive_shift`, since
`pActiveAt` unfolds to `matchActive` at the driver's own field `D'.eta = fun y => D.eta (y + v)`
given by `hD.eta`. -/
theorem Parking.pActiveAt_shift (hD : Parking.PShiftDriver v D' D)
    (hS : LatticeProb.ShiftState v S' S) (t : ℕ) (x : Site d) :
    (Parking.pActiveAt D' S' t x).map (LatticeProb.shiftLabelEmb v) =
      Parking.pActiveAt D S t (x + v) := by
  change (Parking.matchActive D'.eta S' t x).map _ = Parking.matchActive D.eta S t (x + v)
  rw [show D'.eta = fun y => D.eta (y + v) from funext hD.eta]
  exact Parking.matchActive_shift D.eta hS t x

/-- The next position after one step, translated by `v`, equals the next position computed
from the shifted driver and state, since `pNextPos` reads `hS.active`, `hS.pos` and `hD.move`
only through the shifted label `LatticeProb.shiftLabel v p`. -/
theorem Parking.pNextPos_shift (hD : Parking.PShiftDriver v D' D)
    (hS : LatticeProb.ShiftState v S' S) (t : ℕ) (p : Label d) :
    Parking.pNextPos D' S' t p = Parking.pNextPos D S t (LatticeProb.shiftLabel v p) - v := by
  simp only [Parking.pNextPos, hS.active, hS.pos, hD.move]
  split <;> abel

/-- The particle-driven arrivals at a translated site are the image, under the shift
embedding, of the arrivals at the original site, by the candidate-set translation
`candidates_shift` applied at horizon `t + 1` together with `pNextPos_shift`. -/
theorem Parking.pArrivalsAt_shift (hD : Parking.PShiftDriver v D' D)
    (hS : LatticeProb.ShiftState v S' S) (t : ℕ) (x : Site d) :
    (Parking.pArrivalsAt D' S' t x).map (LatticeProb.shiftLabelEmb v) =
      Parking.pArrivalsAt D S t (x + v) := by
  classical
  unfold Parking.pArrivalsAt
  rw [show D'.eta = fun y => D.eta (y + v) from funext hD.eta,
    ← LatticeProb.candidates_shift D.eta x v (t + 1), Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [Function.comp_def, LatticeProb.shiftLabelEmb_apply, hS.active,
    Parking.pNextPos_shift hD hS, sub_eq_iff_eq_add]

/-- Settling of a label is translation-invariant: the rank comparison among the shifted
arrivals transports via `rankIn_shift` and `hr : D'.rank = LatticeProb.shiftRank v D.rank`,
and the hole count at the shifted next position agrees by `hS.holes`. -/
theorem Parking.pSettles_shift (hD : Parking.PShiftDriver v D' D)
    (hS : LatticeProb.ShiftState v S' S) (t : ℕ) (p : Label d) :
    Parking.pSettles D' S' t p = Parking.pSettles D S t (LatticeProb.shiftLabel v p) := by
  classical
  have hr : D'.rank = LatticeProb.shiftRank v D.rank := by
    funext q
    exact hD.rank q.1 q.2
  have hcard := Parking.rankIn_shift v D.rank t _ _
    (Parking.pArrivalsAt_shift hD hS t (Parking.pNextPos D' S' t p)) p
  rw [Parking.pNextPos_shift hD hS, sub_add_cancel] at hcard
  have hhole : S'.holes (Parking.pNextPos D' S' t p) =
      S.holes (Parking.pNextPos D S t (LatticeProb.shiftLabel v p)) := by
    rw [hS.holes, Parking.pNextPos_shift hD hS, sub_add_cancel]
  simp only [rankIn, Parking.matchKey, Prod.Lex.toLex_lt_toLex, ← hr] at hcard
  unfold Parking.pSettles
  rw [hS.active, hhole]
  simp only [labelLT, Parking.pNextPos_shift hD hS, hcard]

/-- One step of the particle-driven state is a `ShiftState`-preserving translation, assembled
from `pSettles_shift`, `pNextPos_shift`, `pArrivalsAt_shift` and `pActiveAt_shift` field by
field. -/
theorem Parking.pStep_shift (hD : Parking.PShiftDriver v D' D)
    (hS : LatticeProb.ShiftState v S' S) (t : ℕ) :
    LatticeProb.ShiftState v (Parking.pStep D' S' t) (Parking.pStep D S t) where
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
    (hA : A'.map (LatticeProb.shiftLabelEmb v) = A) (p : Label d) :
    p ∈ A' ↔ LatticeProb.shiftLabel v p ∈ A := by
  rw [← hA]
  constructor
  · intro hp
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
  · intro hp
    obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hp
    exact (LatticeProb.shiftLabel_injective v he) ▸ hq

/-- Translation of a common-table entry. -/
def Parking.shiftRoundSlot (v : Site d) : Parking.RoundSlot d → Parking.RoundSlot d
  | Sum.inl (x, j) => Sum.inl (x + v, j)
  | Sum.inr p => Sum.inr (LatticeProb.shiftLabel v p)

/-- The translated round-slot map is injective: the two summands `Sum.inl`/`Sum.inr` stay
disjoint, and translation of sites (`add_right_cancel`) and of labels
(`LatticeProb.shiftLabel_injective`) is itself injective on each summand. -/
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
      | inr q => exact congrArg Sum.inr (LatticeProb.shiftLabel_injective v (Sum.inr_injective h))

/-- The common-table noise translated by `v`: at round `t` it reads the original noise `σ`
at the slot translated back by `shiftRoundSlot v`. -/
def Parking.shiftRoundNoise (v : Site d) (σ : Parking.RoundNoise d) : Parking.RoundNoise d :=
  fun t q => σ t (Parking.shiftRoundSlot v q)

/-- Matching uses the translated table entry after translating a state. -/
theorem Parking.matchSlot_shift (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (hS : LatticeProb.ShiftState v S' S) (t : ℕ) (p : Label d) :
    Parking.shiftRoundSlot v
      (Parking.matchSlot (fun y => η (y + v)) (LatticeProb.shiftRank v ρ) S' t p) =
      Parking.matchSlot η ρ S t (LatticeProb.shiftLabel v p) := by
  classical
  have hA : (Parking.matchActive (fun y => η (y + v)) S' t (S'.pos p)).map
      (LatticeProb.shiftLabelEmb v) =
          Parking.matchActive η S t (S.pos (LatticeProb.shiftLabel v p)) := by
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
    LatticeProb.ShiftState v
      (Parking.matchedState (fun y => η (y + v)) (LatticeProb.shiftRank v ρ)
        (Parking.shiftRoundNoise v σ) t)
      (Parking.matchedState η ρ σ t) := by
  induction t with
  | zero =>
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun _ => rfl⟩
      · rfl
      · simp only [Parking.matchedState, initial, LatticeProb.shiftLabel]
        abel
      · rfl
  | succ t ih =>
      apply Parking.pStep_shift _ ih
      refine ⟨fun _ => rfl, ?_, fun _ _ => rfl⟩
      intro p k
      change σ k (Parking.shiftRoundSlot v
        (Parking.matchSlot _ _ _ k p)) =
            σ k (Parking.matchSlot _ _ _ k (LatticeProb.shiftLabel v p))
      rw [Parking.matchSlot_shift η ρ ih]

end
