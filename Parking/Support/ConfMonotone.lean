/-
Raising the configuration in the particle-driven construction.

`Parking.tagged_invariant` compares a configuration with the same one raised by
one at a single site.  What `lem:density-compare` needs is the comparison of
two configurations that differ everywhere, which the paper obtains by applying
the one-site coupling successively; in the particle-driven construction the
comparison is a single induction, because every particle carries its own
displacements and its own uniform variables and those are shared by the two
processes.

The invariant is that a particle active in the lower process is active in the
higher one and stands where it stands there, and that the higher process has no
more unfilled holes anywhere.  The two halves feed each other exactly as in the
one-site coupling: more arrivals and fewer holes both make settling harder.
-/
import Parking.Support.Agree
import Parking.Support.Coupling

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

theorem pState_succ_active (D : LatticeProb.PDriver d) (t : ℕ) (p : Label d) :
    (LatticeProb.pState D (t + 1)).active p
      = ((LatticeProb.pState D t).active p
        && !LatticeProb.pSettles D (LatticeProb.pState D t) t p) := by
  simp [LatticeProb.pState, LatticeProb.pStep]

theorem pState_succ_pos (D : LatticeProb.PDriver d) (t : ℕ) (p : Label d) :
    (LatticeProb.pState D (t + 1)).pos p
      = LatticeProb.pNextPos D (LatticeProb.pState D t) t p := by
  rfl

theorem pState_succ_holes (D : LatticeProb.PDriver d) (t : ℕ) (x : Site d) :
    (LatticeProb.pState D (t + 1)).holes x
      = (LatticeProb.pState D t).holes x
        - (LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t x).card := by
  rfl

theorem pSettles_eq_true_iff (D : LatticeProb.PDriver d) (S : State d) (t : ℕ)
    (p : Label d) :
    LatticeProb.pSettles D S t p = true ↔
      (S.active p = true ∧
        ((LatticeProb.pArrivalsAt D S t (LatticeProb.pNextPos D S t p)).filter
          fun q => D.rank (q, t) < D.rank (p, t) ∨
            (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card
          < S.holes (LatticeProb.pNextPos D S t p)) := by
  simp [LatticeProb.pSettles]

/-- **Raising the configuration keeps particles active and fills holes.** -/
theorem pMono {D D' : LatticeProb.PDriver d} (hmove : D'.move = D.move)
    (hrank : D'.rank = D.rank) (hconf : ∀ x, D.eta x ≤ D'.eta x) :
    ∀ t : ℕ,
      (∀ p : Label d, (LatticeProb.pState D t).active p = true →
        (LatticeProb.pState D' t).active p = true ∧
          (LatticeProb.pState D' t).pos p = (LatticeProb.pState D t).pos p) ∧
      (∀ x : Site d, (LatticeProb.pState D' t).holes x
        ≤ (LatticeProb.pState D t).holes x) := by
  intro t
  induction t with
  | zero =>
      refine ⟨fun p hp => ⟨?_, rfl⟩, fun x => ?_⟩
      · have h1 : p.2 < (D.eta p.1).toNat := by
          simpa [LatticeProb.pState, initial] using hp
        have h2 := hconf p.1
        show decide (p.2 < (D'.eta p.1).toNat) = true
        simp only [decide_eq_true_eq]
        omega
      · show (-(D'.eta x)).toNat ≤ (-(D.eta x)).toNat
        have := hconf x
        omega
  | succ t ih =>
      obtain ⟨iha, ihh⟩ := ih
      have hnext : ∀ p : Label d, (LatticeProb.pState D t).active p = true →
          LatticeProb.pNextPos D' (LatticeProb.pState D' t) t p
            = LatticeProb.pNextPos D (LatticeProb.pState D t) t p := by
        intro p hp
        obtain ⟨hp', hpos⟩ := iha p hp
        show (if (LatticeProb.pState D' t).active p
              then (LatticeProb.pState D' t).pos p + D'.move (p, t)
              else (LatticeProb.pState D' t).pos p)
            = (if (LatticeProb.pState D t).active p
              then (LatticeProb.pState D t).pos p + D.move (p, t)
              else (LatticeProb.pState D t).pos p)
        rw [if_pos hp', if_pos hp, hpos, hmove]
      have harr : ∀ x : Site d,
          LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t x
            ⊆ LatticeProb.pArrivalsAt D' (LatticeProb.pState D' t) t x := by
        intro x q hq
        rw [LatticeProb.pArrivalsAt, Finset.mem_filter] at hq ⊢
        obtain ⟨hcand, hact, hpos⟩ := hq
        exact ⟨candidates_mono hconf x (t + 1) hcand, (iha q hact).1,
          by rw [hnext q hact]; exact hpos⟩
      have hholes : ∀ x : Site d,
          (LatticeProb.pState D' (t + 1)).holes x
            ≤ (LatticeProb.pState D (t + 1)).holes x := by
        intro x
        rw [pState_succ_holes, pState_succ_holes]
        have h1 := ihh x
        have h2 := Finset.card_le_card (harr x)
        omega
      refine ⟨fun p hp => ?_, hholes⟩
      rw [pState_succ_active, Bool.and_eq_true, Bool.not_eq_true'] at hp
      obtain ⟨hact, hset⟩ := hp
      obtain ⟨hact', hpos'⟩ := iha p hact
      have hy := hnext p hact
      have hfilt : ((LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t
              (LatticeProb.pNextPos D (LatticeProb.pState D t) t p)).filter
            fun q => D.rank (q, t) < D.rank (p, t) ∨
              (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card
          ≤ ((LatticeProb.pArrivalsAt D' (LatticeProb.pState D' t) t
              (LatticeProb.pNextPos D (LatticeProb.pState D t) t p)).filter
            fun q => D'.rank (q, t) < D'.rank (p, t) ∨
              (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p)).card := by
        rw [hrank]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (harr _))
      have hge : (LatticeProb.pState D t).holes
            (LatticeProb.pNextPos D (LatticeProb.pState D t) t p)
          ≤ ((LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t
              (LatticeProb.pNextPos D (LatticeProb.pState D t) t p)).filter
            fun q => D.rank (q, t) < D.rank (p, t) ∨
              (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card := by
        by_contra hlt
        rw [not_le] at hlt
        have hs := (pSettles_eq_true_iff D (LatticeProb.pState D t) t p).mpr ⟨hact, hlt⟩
        rw [hs] at hset
        exact Bool.noConfusion hset
      have hnotset : LatticeProb.pSettles D' (LatticeProb.pState D' t) t p = false := by
        rw [← Bool.not_eq_true]
        intro hc
        obtain ⟨-, hlt'⟩ := (pSettles_eq_true_iff D' (LatticeProb.pState D' t) t p).mp hc
        rw [hy] at hlt'
        have h1 := ihh (LatticeProb.pNextPos D (LatticeProb.pState D t) t p)
        omega
      refine ⟨?_, ?_⟩
      · rw [pState_succ_active, hact', hnotset]
        rfl
      · rw [pState_succ_pos, pState_succ_pos]
        exact hy

/-- The particles which started at a site and are still active, in the
particle-driven construction. -/
def pSurvivorsFrom (D : LatticeProb.PDriver d) (t : ℕ) (y : Site d) : ℕ :=
  ((Finset.range (D.eta y).toNat).filter fun i =>
    (LatticeProb.pState D t).active (y, i)).card

/-- Raising the configuration raises the survivor count. -/
theorem pSurvivorsFrom_mono {D D' : LatticeProb.PDriver d} (hmove : D'.move = D.move)
    (hrank : D'.rank = D.rank) (hconf : ∀ x, D.eta x ≤ D'.eta x) (t : ℕ) (y : Site d) :
    pSurvivorsFrom D t y ≤ pSurvivorsFrom D' t y := by
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
  refine ⟨?_, ((pMono hmove hrank hconf t).1 (y, i) hi.2).1⟩
  have := hconf y
  omega

end Parking

end
