/-
"Neither process has an active particle and an unfilled hole at the same site"
(`parking.tex:1281-1283`), the fact that makes all the unmatched particles and
holes created at one site carry the same sign in Step 1 of `lem:critical-density`.

It holds for one process, at every time and every site.  Initially a site with an
active particle has a positive count, so no hole.  After a round, a particle
active at `x` arrived there and did not settle, which means that the arrivals of
smaller rank than it already number at least the holes; that particle is itself
an arrival and is not among them, so the arrivals outnumber the holes strictly
and the holes are exhausted.
-/
import Parking.Support.Reads

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- **No site carries an active particle and an unfilled hole.** -/
theorem holeCount_eq_zero_of_activeCount_pos {D : Driver d}
    (t : ℕ) (x : Site d) (h : 0 < LatticeProb.activeCount D t x) :
    LatticeProb.holeCount D t x = 0 := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [LatticeProb.activeAt, Finset.mem_filter] at hp
  obtain ⟨hcand, hact, hpos⟩ := hp
  cases t with
  | zero =>
      have hlt : p.2 < (D.eta p.1).toNat := by
        have : (decide (p.2 < (D.eta p.1).toNat)) = true := hact
        simpa using this
      have hxp : p.1 = x := hpos
      rw [hxp] at hlt
      have hpos' : 0 < (D.eta x).toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      have : 0 < D.eta x := by omega
      show (LatticeProb.state D 0).holes x = 0
      show (-D.eta x).toNat = 0
      omega
  | succ s =>
      set S := LatticeProb.state D s with hS
      have hactS : S.active p = true ∧ (LatticeProb.settles D S s p) = false := by
        have h2 : (LatticeProb.state D (s + 1)).active p = true := hact
        rw [show LatticeProb.state D (s + 1) = LatticeProb.step D S s from rfl] at h2
        simp only [LatticeProb.step, decide_eq_true_eq, Bool.not_eq_true'] at h2
        exact h2
      have hnext : LatticeProb.nextPos D S s p = x := hpos
      have hmem : p ∈ LatticeProb.arrivalsAt D S s x := by
        rw [LatticeProb.arrivalsAt, Finset.mem_filter]
        exact ⟨hcand, hactS.1, hnext⟩
      -- the arrivals of smaller rank than `p` are at least the holes
      have hns : ¬ (((LatticeProb.arrivalsAt D S s (LatticeProb.nextPos D S s p)).filter
          fun q => D.rank (q, s) < D.rank (p, s) ∨
            (D.rank (q, s) = D.rank (p, s) ∧ LatticeProb.labelLT q p)).card
          < S.holes (LatticeProb.nextPos D S s p)) := by
        intro hlt
        have : LatticeProb.settles D S s p = true := by
          rw [LatticeProb.settles]
          simp only [decide_eq_true_eq]
          exact ⟨hactS.1, hlt⟩
        rw [hactS.2] at this
        exact Bool.noConfusion this
      rw [hnext] at hns
      rw [not_lt] at hns
      -- `p` is an arrival but is not of smaller rank than itself
      have hsub : ((LatticeProb.arrivalsAt D S s x).filter
          fun q => D.rank (q, s) < D.rank (p, s) ∨
            (D.rank (q, s) = D.rank (p, s) ∧ LatticeProb.labelLT q p))
          ⊆ (LatticeProb.arrivalsAt D S s x).erase p := by
        intro q hq
        rw [Finset.mem_filter] at hq
        refine Finset.mem_erase.mpr ⟨?_, hq.1⟩
        intro hqp
        subst hqp
        rcases hq.2 with hlt | ⟨-, hlt⟩
        · exact lt_irrefl _ hlt
        · exact LatticeProb.labelLT_irrefl q hlt
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hmem] at hcard
      have hpos1 : 1 ≤ (LatticeProb.arrivalsAt D S s x).card := Finset.card_pos.mpr ⟨p, hmem⟩
      have hstrict : S.holes x < (LatticeProb.arrivalsAt D S s x).card := by omega
      show (LatticeProb.state D (s + 1)).holes x = 0
      show S.holes x - (LatticeProb.arrivalsAt D S s x).card = 0
      omega

/-- The same fact for the data of the parking process. -/
theorem H_eq_zero_of_A_pos (ω : Data d)
    (t : ℕ) (x : Site d) (h : 0 < Parking.A ω t x) : Parking.H ω t x = 0 :=
  holeCount_eq_zero_of_activeCount_pos t x h

end Parking

end
