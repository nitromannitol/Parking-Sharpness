/-
`F Z = 0` at the level of the realization with the tagged particle put back
(`parking.tex:2448-2455`).

While the tagged particle is active it walks along the prescribed path, so the
sites it has visited are exactly `R_t`; a particle still active at time `t` has
settled in no round, so by `Parking.pHoleCount_visited_eq_zero` each of those
sites carries no unfilled hole at time `t`.  At the origin there is no hole to
begin with, because the origin carries the prescribed particles.
-/
import Parking.Support.SurvivorHoles
import Parking.Support.SubcriticalPair

open LatticeProb Finset

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The moves of the tagged particle are the prescribed walk. -/
theorem taggedMove_zero (w : ℕ → Fin d × Bool) (m : Label d × ℕ → Fin d × Bool) (s : ℕ) :
    taggedMove w m ((0, 0), s) = w s := by
  simp [taggedMove]

/-- **While it is active the tagged particle stands on the prescribed walk.** -/
theorem taggedDriver_pos (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) {t : ℕ}
    (h : (pState (taggedDriver w rk ω) t).active (0, 0) = true) :
    ∀ s, s ≤ t → (pState (taggedDriver w rk ω) s).pos (0, 0) = walkPath (0 : Site d) w s := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
      intro hs
      have hact : (pState (taggedDriver w rk ω) s).active (0, 0) = true :=
        pActive_of_le _ _ (by omega) h
      rw [pPos_succ, pNextPos_of_active _ _ s _ hact, ih (by omega)]
      rw [show (taggedDriver w rk ω).move (((0 : Site d), 0), s) = w s from
        taggedMove_zero w ω.2.1 s]
      rfl

/-- **No site of the range carries an unfilled hole once the tagged particle has
survived to time `t`.** -/
theorem taggedDriver_holeCount_range (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) {t : ℕ}
    (hη : (0 : ℤ) ≤ ω.1 0)
    (h : (pState (taggedDriver w rk ω) t).active (0, 0) = true) :
    ∀ x ∈ rangeFinset (0 : Site d) w t, pHoleCount (taggedDriver w rk ω) t x = 0 := by
  intro x hx
  simp only [rangeFinset, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hjt : j ≤ t := Nat.lt_succ_iff.mp hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have h0 : pHoleCount (taggedDriver w rk ω) 0 (walkPath (0 : Site d) w 0) = 0 := by
      show ((-(addParticle 0 ω.1) (walkPath (0 : Site d) w 0)).toNat = 0)
      have hx0 : walkPath (0 : Site d) w 0 = 0 := rfl
      rw [hx0]
      simp only [addParticle]
      omega
    exact Nat.le_zero.mp (le_trans (pHoleCount_antitone _ _ (Nat.zero_le t)) (le_of_eq h0))
  · rw [← taggedDriver_pos w rk ω h j hjt]
    exact pHoleCount_visited_eq_zero _ h hj1 hjt

/-- **A particle still active has filled no hole**: adding it to the process
leaves every hole count where it was.  In the first alternative of
`lem:one-particle` the hole counts agree; the second alternative gives the added
label the activity it has in the smaller process, where its index is not below
the count. -/
theorem pHoleCount_addParticleDriver_eq_of_active (D : PDriver d) (x₀ : Site d) (t : ℕ)
    (h : (pState (addParticleDriver x₀ D) t).active (x₀, (D.eta x₀).toNat) = true) (x : Site d) :
    pHoleCount (addParticleDriver x₀ D) t x = pHoleCount D t x := by
  rcases oneParticleInv_all (labelOrder d) D x₀ t with
    ⟨u, hu1, hu2, hother, hholes⟩ | ⟨hact, z, hz, hzo⟩
  · exact hholes x
  · exfalso
    have h2 : (pState D t).active (x₀, (D.eta x₀).toNat) = true := by
      rw [← hact]
      exact h
    exact absurd (lt_toNat_of_pActive h2) (lt_irrefl _)

end Parking

end
