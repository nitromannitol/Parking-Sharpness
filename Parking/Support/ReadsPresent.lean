/-
The particle-driven construction reads the particles PRESENT and nothing else.

A site with count `k` carries the `k` particles labelled `0, …, k-1`.  A label
whose index is at or above the count at its site carries no particle: it is
inactive at time zero, it stays inactive, it never belongs to a candidate set,
and it never arrives anywhere.  So altering the walk or the uniform variables
attached to such a label changes no state of the process.

This is the second clause of `Parking.RelabelInvariant`, `Parking.ReadsParticles`,
for every observable built from the states of the process.
-/
import Parking.Support.Particle

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- Two states with the same fields are equal. -/
theorem state_ext {A B : State d} (h1 : ∀ p, A.active p = B.active p)
    (h2 : ∀ p, A.pos p = B.pos p) (h3 : ∀ x, A.holes x = B.holes x)
    (h4 : ∀ x, A.departures x = B.departures x) : A = B := by
  cases A; cases B
  simp only [State.mk.injEq]
  exact ⟨funext h1, funext h2, funext h3, funext h4⟩

/-- An active label carries a particle: its index is below the count at its
site. -/
theorem pState_active_lt (D : PDriver d) :
    ∀ (t : ℕ) (p : Label d), (pState D t).active p = true → p.2 < (D.eta p.1).toNat
  | 0, p, hp => of_decide_eq_true hp
  | t + 1, p, hp => by
      have h1 : (pState D (t + 1)).active p
          = decide ((pState D t).active p = true ∧ (!pSettles D (pState D t) t p) = true) := rfl
      rw [h1] at hp
      exact pState_active_lt D t p (of_decide_eq_true hp).1

/-- Two drivers with the same counts whose walks and uniform variables agree at
every label that carries a particle. -/
structure AgreesOnPresent (D E : PDriver d) : Prop where
  /-- The counts are the same. -/
  eta : ∀ x, D.eta x = E.eta x
  /-- The walks agree at the labels that carry a particle. -/
  move : ∀ (p : Label d) (t : ℕ), p.2 < (D.eta p.1).toNat → D.move (p, t) = E.move (p, t)
  /-- The uniform variables agree at the labels that carry a particle. -/
  rank : ∀ (p : Label d) (t : ℕ), p.2 < (D.eta p.1).toNat → D.rank (p, t) = E.rank (p, t)

variable {D E : PDriver d}

/-- The candidate sets are the same. -/
theorem candidates_present (h : AgreesOnPresent D E) (y : Site d) (r : ℕ) :
    candidates D.eta y r = candidates E.eta y r := by
  rw [funext h.eta]

/-- The active particles at a site are the same. -/
theorem pActiveAt_present (h : AgreesOnPresent D E) (S : State d) (t : ℕ) (y : Site d) :
    pActiveAt D S t y = pActiveAt E S t y := by
  simp only [pActiveAt, candidates_present h]

/-- A label steps to the same site under both drivers. -/
theorem pNextPos_present (h : AgreesOnPresent D E) {S : State d}
    (hS : ∀ p, S.active p = true → p.2 < (D.eta p.1).toNat) (t : ℕ) (p : Label d) :
    pNextPos D S t p = pNextPos E S t p := by
  by_cases hp : S.active p = true
  · simp only [pNextPos, hp, if_pos, h.move p t (hS p hp)]
  · simp only [Bool.not_eq_true] at hp
    simp only [pNextPos, hp, Bool.false_eq_true, if_false]

/-- The particles arriving at a site are the same. -/
theorem pArrivalsAt_present (h : AgreesOnPresent D E) {S : State d}
    (hS : ∀ p, S.active p = true → p.2 < (D.eta p.1).toNat) (t : ℕ) (x : Site d) :
    pArrivalsAt D S t x = pArrivalsAt E S t x := by
  simp only [pArrivalsAt, candidates_present h, pNextPos_present h hS t]

/-- A label settles under one driver exactly when it settles under the other. -/
theorem pSettles_present (h : AgreesOnPresent D E) {S : State d}
    (hS : ∀ p, S.active p = true → p.2 < (D.eta p.1).toNat) (t : ℕ) (p : Label d) :
    pSettles D S t p = pSettles E S t p := by
  classical
  by_cases hp : S.active p = true
  · have hrank : ∀ q ∈ pArrivalsAt D S t (pNextPos D S t p), D.rank (q, t) = E.rank (q, t) := by
      intro q hq
      exact h.rank q t (LatticeProb.mem_candidates_iff.mp (Finset.mem_filter.mp hq).1).2
    have hpos : pNextPos E S t p = pNextPos D S t p := (pNextPos_present h hS t p).symm
    have hA : pArrivalsAt E S t (pNextPos E S t p) = pArrivalsAt D S t (pNextPos D S t p) := by
      rw [hpos, pArrivalsAt_present h hS t]
    have hfil : ((pArrivalsAt E S t (pNextPos E S t p)).filter fun q =>
          E.rank (q, t) < E.rank (p, t) ∨ (E.rank (q, t) = E.rank (p, t) ∧ labelLT q p))
        = ((pArrivalsAt D S t (pNextPos D S t p)).filter fun q =>
          D.rank (q, t) < D.rank (p, t) ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)) := by
      rw [hA]
      refine Finset.filter_congr fun q hq => ?_
      rw [hrank q hq, h.rank p t (hS p hp)]
    simp only [pSettles]
    rw [hfil, hpos]
  · simp only [Bool.not_eq_true] at hp
    simp only [pSettles, hp, Bool.false_eq_true, false_and]

/-- One round is the same under both drivers. -/
theorem pStep_present (h : AgreesOnPresent D E) {S : State d}
    (hS : ∀ p, S.active p = true → p.2 < (D.eta p.1).toNat) (t : ℕ) :
    pStep D S t = pStep E S t :=
  state_ext (fun p => by simp only [pStep, pSettles_present h hS t p])
    (fun p => pNextPos_present h hS t p)
    (fun x => by simp only [pStep, pArrivalsAt_present h hS t x])
    (fun y => by simp only [pStep, pActiveAt_present h S t y])

/-- **The process reads the particles present alone.**  Two drivers with the
same counts whose walks and uniform variables agree at every label carrying a
particle have the same state at every time. -/
theorem pState_present (h : AgreesOnPresent D E) : ∀ t : ℕ, pState D t = pState E t
  | 0 => by
      refine state_ext (fun p => ?_) (fun _ => rfl) (fun x => ?_) (fun _ => rfl)
      · simp only [pState, LatticeProb.initial, h.eta]
      · simp only [pState, LatticeProb.initial, h.eta]
  | t + 1 => by
      have ih := pState_present h t
      have hS : ∀ p, (pState D t).active p = true → p.2 < (D.eta p.1).toNat :=
        pState_active_lt D t
      show pStep D (pState D t) t = pStep E (pState E t) t
      rw [← ih]
      exact pStep_present h hS t


/-- The hypothesis of `Parking.ReadsParticles` gives two drivers agreeing on the
particles present. -/
theorem agreesOnPresent_of_reads {ω ω' : PData d} (hc : ω.1 = ω'.1)
    (hm : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q) :
    AgreesOnPresent (toPDriver ω) (toPDriver ω') :=
  ⟨fun x => congrFun hc x, fun p t hp => hm (p, t) hp, fun p t hp => hr (p, t) hp⟩

/-- **Altering the data of a label that carries no particle changes no state.**
This is what `Parking.ReadsParticles` asks of an observable of the process. -/
theorem pState_congr_of_reads {ω ω' : PData d} (hc : ω.1 = ω'.1)
    (hm : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q) (t : ℕ) :
    pState (toPDriver ω) t = pState (toPDriver ω') t :=
  pState_present (agreesOnPresent_of_reads hc hm hr) t

/-- The hole counts read the particles present alone. -/
theorem pHoleCount_reads {ω ω' : PData d} (hc : ω.1 = ω'.1)
    (hm : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q)
    (t : ℕ) (x : Site d) :
    pHoleCount (toPDriver ω) t x = pHoleCount (toPDriver ω') t x := by
  simp only [pHoleCount, pState_congr_of_reads hc hm hr t]

end Parking

end
