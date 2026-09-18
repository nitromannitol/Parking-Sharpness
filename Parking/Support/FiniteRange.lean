/-
Finite range of dependence for the particle-driven construction.

`thm:subcritical` applies `lem:product` to two observables of the process at
time `t`, and `lem:product` asks that they be functions of the data at finitely
many sites (`parking.tex:2465`).  The state after `s` rounds inside a box of
radius `r` is determined by the data inside the box of radius `r + s(s+1)`: a
particle arriving somewhere in the box at round `s + 1` started within `s + 1`
of it, and whether it settles is decided by the arrivals at its own new site,
which lies a further `s + 1` out, so each round costs two steps of radius,
`2(s+1)` in all.
-/
import Parking.Support.Coupling

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- A particle that starts inside a box stays inside the box grown by the number
of rounds. -/
theorem pPos_mem_boxFinset (D : PDriver d) {y : Site d} {r : ℕ} (t : ℕ) {p : Label d}
    (hp : p.1 ∈ boxFinset y r) : (pState D t).pos p ∈ boxFinset y (r + t) :=
  mem_boxFinset_add hp (mem_boxFinset_iff.mpr fun i => abs_pPos_sub_start_le D t p i)

/-- The candidate set reads the counts inside the box alone. -/
theorem candidates_congr {η η' : Site d → ℤ} {y : Site d} {r : ℕ}
    (h : ∀ x ∈ boxFinset y r, η x = η' x) : candidates η y r = candidates η' y r := by
  ext p
  rw [mem_candidates_iff, mem_candidates_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [← h p.1 (mem_boxFinset_iff.mpr h1)]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [h p.1 (mem_boxFinset_iff.mpr h1)]⟩

/-- Two drivers agreeing on the counts, the walks and the uniform variables of
every site of a box. -/
structure AgreesOnBox (z : Site d) (ρ : ℕ) (D E : PDriver d) : Prop where
  eta : ∀ x ∈ boxFinset z ρ, D.eta x = E.eta x
  move : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset z ρ → D.move q = E.move q
  rank : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset z ρ → D.rank q = E.rank q

variable {z : Site d} {ρ : ℕ} {D E : PDriver d}

/-- The arrivals at a site of the box are the same for both drivers, once the
states agree on the box grown by one round. -/
theorem pArrivalsAt_congr_box (h : AgreesOnBox z ρ D E) {s r₀ r : ℕ}
    (hrρ : r ≤ ρ) (hr : r₀ + (s + 1) ≤ r)
    (hstate : ∀ p : Label d, p.1 ∈ boxFinset z r →
      (pState D s).active p = (pState E s).active p ∧ (pState D s).pos p = (pState E s).pos p)
    {y : Site d} (hy : y ∈ boxFinset z r₀) :
    pArrivalsAt D (pState D s) s y = pArrivalsAt E (pState E s) s y := by
  classical
  have hbox : ∀ x ∈ boxFinset y (s + 1), x ∈ boxFinset z r := fun x hx =>
    boxFinset_mono hr (mem_boxFinset_add hy hx)
  have hcand : candidates D.eta y (s + 1) = candidates E.eta y (s + 1) :=
    candidates_congr fun x hx => h.eta x (boxFinset_mono hrρ (hbox x hx))
  unfold pArrivalsAt
  rw [hcand]
  refine Finset.filter_congr fun p hp => ?_
  have hp1 : p.1 ∈ boxFinset z r :=
    hbox p.1 (mem_boxFinset_iff.mpr (mem_candidates_iff.mp hp).1)
  obtain ⟨hact, hpos⟩ := hstate p hp1
  have hmv : D.move (p, s) = E.move (p, s) := h.move (p, s) (boxFinset_mono hrρ hp1)
  have hnext : pNextPos D (pState D s) s p = pNextPos E (pState E s) s p := by
    unfold pNextPos
    rw [hact, hpos, hmv]
  rw [hact, hnext]

set_option maxHeartbeats 1000000 in
/-- **The state after `s` rounds inside a box of radius `r` is determined by the
data inside the box of radius `r + s(s+1)`.** -/
theorem pState_agree_box (h : AgreesOnBox z ρ D E) :
    ∀ s r : ℕ, r + s * (s + 1) ≤ ρ →
      (∀ y ∈ boxFinset z r, (pState D s).holes y = (pState E s).holes y) ∧
      (∀ p : Label d, p.1 ∈ boxFinset z r →
        (pState D s).active p = (pState E s).active p ∧
          (pState D s).pos p = (pState E s).pos p) := by
  classical
  intro s
  induction s with
  | zero =>
      intro r hr
      have hrρ : r ≤ ρ := by simpa using hr
      refine ⟨fun y hy => ?_, fun p hp => ⟨?_, rfl⟩⟩
      · simp only [pState, LatticeProb.initial]
        rw [h.eta y (boxFinset_mono hrρ hy)]
      · simp only [pState, LatticeProb.initial]
        rw [h.eta p.1 (boxFinset_mono hrρ hp)]
  | succ s ih =>
      intro r hr
      have hkey : r + 2 * (s + 1) + s * (s + 1) = r + (s + 1) * (s + 1 + 1) := by ring
      have hr' : r + 2 * (s + 1) + s * (s + 1) ≤ ρ := by rw [hkey]; exact hr
      obtain ⟨ihholes, ihstate⟩ := ih (r + 2 * (s + 1)) hr'
      have hrρ : r + 2 * (s + 1) ≤ ρ := by omega
      have harr : ∀ r₀ : ℕ, r₀ + (s + 1) ≤ r + 2 * (s + 1) → ∀ y ∈ boxFinset z r₀,
          pArrivalsAt D (pState D s) s y = pArrivalsAt E (pState E s) s y :=
        fun r₀ hr₀ y hy => pArrivalsAt_congr_box h hrρ hr₀ ihstate hy
      refine ⟨fun y hy => ?_, fun p hp => ?_⟩
      · rw [pHoles_succ, pHoles_succ, ihholes y (boxFinset_mono (by omega) hy),
          harr r (by omega) y hy]
      · obtain ⟨hact, hpos⟩ := ihstate p (boxFinset_mono (by omega) hp)
        have hmv : D.move (p, s) = E.move (p, s) :=
          h.move (p, s) (boxFinset_mono (by omega) hp)
        have hnext : pNextPos D (pState D s) s p = pNextPos E (pState E s) s p := by
          simp only [pNextPos, hact, hpos, hmv]
        have hnextbox : pNextPos D (pState D s) s p ∈ boxFinset z (r + s + 1) := by
          by_cases hA : (pState D s).active p = true
          · rw [pNextPos_of_active D _ s p hA]
            exact mem_boxFinset_add (pPos_mem_boxFinset D s hp)
              (mem_boxFinset_iff.mpr fun i => by
                simpa using abs_stepVec_le_one (D.move (p, s)) i)
          · have hEq : pNextPos D (pState D s) s p = (pState D s).pos p := by
              simp only [pNextPos]
              rw [if_neg hA]
            rw [hEq]
            exact boxFinset_mono (by omega) (pPos_mem_boxFinset D s hp)
        have harr' : pArrivalsAt D (pState D s) s (pNextPos D (pState D s) s p)
            = pArrivalsAt E (pState E s) s (pNextPos E (pState E s) s p) := by
          rw [← hnext]
          exact harr (r + s + 1) (by omega) _ hnextbox
        have hholes' : (pState D s).holes (pNextPos D (pState D s) s p)
            = (pState E s).holes (pNextPos E (pState E s) s p) := by
          rw [← hnext]
          exact ihholes _ (boxFinset_mono (by omega) hnextbox)
        have hrank : ∀ q : Label d,
            q ∈ pArrivalsAt D (pState D s) s (pNextPos D (pState D s) s p) →
            D.rank (q, s) = E.rank (q, s) := by
          intro q hq
          have hq1 : q.1 ∈ boxFinset z (r + s + 1 + (s + 1)) :=
            mem_boxFinset_of_mem_candidates hnextbox (Finset.mem_filter.mp hq).1
          exact h.rank (q, s) (boxFinset_mono (by omega) hq1)
        have hrp : D.rank (p, s) = E.rank (p, s) :=
          h.rank (p, s) (boxFinset_mono (by omega) hp)
        have hfilter :
            ((pArrivalsAt D (pState D s) s (pNextPos D (pState D s) s p)).filter fun q =>
                D.rank (q, s) < D.rank (p, s) ∨
                  (D.rank (q, s) = D.rank (p, s) ∧ labelLT q p))
              = ((pArrivalsAt E (pState E s) s (pNextPos E (pState E s) s p)).filter fun q =>
                E.rank (q, s) < E.rank (p, s) ∨
                  (E.rank (q, s) = E.rank (p, s) ∧ labelLT q p)) := by
          rw [← harr']
          refine Finset.filter_congr fun q hq => ?_
          rw [hrank q hq, hrp]
        have hcard := congrArg Finset.card hfilter
        have hsettle : pSettles D (pState D s) s p = pSettles E (pState E s) s p := by
          simp only [pSettles, hact, hholes', hcard]
        refine ⟨?_, by rw [pPos_succ, pPos_succ, hnext]⟩
        rw [Bool.eq_iff_iff, pActive_succ_iff, pActive_succ_iff, hact, hsettle]

/-- The hole counts inside a box are read off the data of the grown box. -/
theorem pHoleCount_congr_box (h : AgreesOnBox z ρ D E) {t r : ℕ} (hr : r + t * (t + 1) ≤ ρ)
    {y : Site d} (hy : y ∈ boxFinset z r) : pHoleCount D t y = pHoleCount E t y :=
  (pState_agree_box h t r hr).1 y hy

/-- The activity of a particle of the box is read off the data of the grown box. -/
theorem pState_active_congr_box (h : AgreesOnBox z ρ D E) {t r : ℕ} (hr : r + t * (t + 1) ≤ ρ)
    {p : Label d} (hp : p.1 ∈ boxFinset z r) :
    (pState D t).active p = (pState E t).active p :=
  ((pState_agree_box h t r hr).2 p hp).1

end Parking

end
