/-
The first half of Step 1 of `thm:subcritical` (`parking.tex:2448-2455`).

"On `{F = 1}`, particle 1 fills no hole... Every hole at a site it visits is
filled by the end of that round.  Thus no site of `R_t` carries an unfilled hole
at time `t`."

A particle that does not settle in a round sees at least as many arrivals of
smaller rank ahead of it as there are holes at its new site, so the holes there,
which shrink by the number of arrivals, are exhausted in that round; and hole
counts never grow.  A particle still active at time `t` has settled in no round
up to `t`, so every site it has visited carries no unfilled hole at time `t`.
-/
import Parking.Support.Coupling

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- Hole counts never grow. -/
theorem pHoleCount_succ_le (D : PDriver d) (t : ℕ) (x : Site d) :
    pHoleCount D (t + 1) x ≤ pHoleCount D t x := by
  simp only [pHoleCount, pHoles_succ]
  exact Nat.sub_le _ _

/-- Hole counts are nonincreasing in time. -/
theorem pHoleCount_antitone (D : PDriver d) (x : Site d) {s t : ℕ} (h : s ≤ t) :
    pHoleCount D t x ≤ pHoleCount D s x := by
  induction t with
  | zero => simpa using le_of_eq (by rw [Nat.le_zero.mp h])
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact le_trans (pHoleCount_succ_le D t x) (ih (Nat.lt_succ_iff.mp hlt))
      · rw [Nat.le_antisymm h hge]

/-- Activity is nonincreasing in time. -/
theorem pActive_of_le (D : PDriver d) (p : Label d) {s t : ℕ} (h : s ≤ t)
    (ht : (pState D t).active p = true) : (pState D s).active p = true := by
  induction t with
  | zero => rwa [Nat.le_zero.mp h]
  | succ t ih =>
      have hprev : (pState D t).active p = true := ((pActive_succ_iff D t p).mp ht).1
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact ih (Nat.lt_succ_iff.mp hlt) hprev
      · rwa [Nat.le_antisymm h hge]

/-- **A particle that does not settle exhausts the holes at its new site.** -/
theorem pHoles_succ_eq_zero_of_not_settles (D : PDriver d) (S : State d) (s : ℕ) (p : Label d)
    (hact : S.active p = true) (hns : pSettles D S s p = false) :
    (pStep D S s).holes (pNextPos D S s p) = 0 := by
  classical
  have hnot : ¬ (((pArrivalsAt D S s (pNextPos D S s p)).filter fun q =>
      D.rank (q, s) < D.rank (p, s) ∨ (D.rank (q, s) = D.rank (p, s) ∧ labelLT q p)).card
        < S.holes (pNextPos D S s p)) := by
    intro hlt
    rw [pSettles] at hns
    simp [hact, hlt] at hns
  have hle : S.holes (pNextPos D S s p)
      ≤ ((pArrivalsAt D S s (pNextPos D S s p)).filter fun q =>
        D.rank (q, s) < D.rank (p, s) ∨ (D.rank (q, s) = D.rank (p, s) ∧ labelLT q p)).card :=
    Nat.le_of_not_lt hnot
  have hsub : ((pArrivalsAt D S s (pNextPos D S s p)).filter fun q =>
      D.rank (q, s) < D.rank (p, s) ∨ (D.rank (q, s) = D.rank (p, s) ∧ labelLT q p)).card
        ≤ (pArrivalsAt D S s (pNextPos D S s p)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  show S.holes (pNextPos D S s p) - (pArrivalsAt D S s (pNextPos D S s p)).card = 0
  omega

/-- A particle still active after a round leaves no unfilled hole where it
stands. -/
theorem pHoleCount_pos_succ_eq_zero (D : PDriver d) (t : ℕ) (p : Label d)
    (h : (pState D (t + 1)).active p = true) :
    pHoleCount D (t + 1) ((pState D (t + 1)).pos p) = 0 := by
  obtain ⟨hact, hns⟩ := (pActive_succ_iff D t p).mp h
  rw [pPos_succ]
  exact pHoles_succ_eq_zero_of_not_settles D (pState D t) t p hact hns

/-- **Every site a particle still active at time `t` has visited after the first
round carries no unfilled hole at time `t`.** -/
theorem pHoleCount_visited_eq_zero (D : PDriver d) {t s : ℕ} {p : Label d}
    (h : (pState D t).active p = true) (hs : 1 ≤ s) (hst : s ≤ t) :
    pHoleCount D t ((pState D s).pos p) = 0 := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hact : (pState D (s' + 1)).active p = true := pActive_of_le D p hst h
  have hzero := pHoleCount_pos_succ_eq_zero D s' p hact
  exact Nat.le_zero.mp (le_trans (pHoleCount_antitone D _ hst) (le_of_eq hzero))

end Parking

end
