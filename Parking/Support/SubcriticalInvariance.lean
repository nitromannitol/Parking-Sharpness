/-
The two observables of `thm:subcritical` are invariant under relabeling the
particles at a site (`parking.tex:2321-2332`, `parking.tex:2434-2447`).

`Z` is a sum of hole counts of the realization itself, so it inherits the
equivariance of the particle-driven construction directly.  `F` is read off the
tagged realization, whose uniform variables are those of `ω` at the non-tagged
labels and the prescribed ones at the tagged label; there the equivariance is
`Parking.taggedActive_relabelAt`.

The second clause, that the observables read the particles present alone, is
`Support/ReadsPresent.lean` for `Z` and, for `F`, the observation that the
tagged realization of two realizations agreeing at the particles present again
agree at the particles present: the tagged label carries the prescribed data in
both, and the label `(0, j + 1)` of the tagged realization carries the data of
the label `(0, j)` of the realization, which is present exactly when `(0, j+1)`
is present in the tagged one.
-/
import Parking.Support.SubcriticalRelabel
import Parking.Support.ReadsPresent
import Parking.Support.SubcriticalDepends

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The tagged realizations of two realizations that agree at the particles
present agree at the particles present. -/
theorem agreesOnPresent_taggedDriver (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {ω ω' : PData d}
    (hc : ω.1 = ω'.1)
    (hm : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q) :
    AgreesOnPresent (taggedDriver w r ω) (taggedDriver w r ω') := by
  refine ⟨fun x => by rw [show (taggedDriver w r ω).eta = addParticle 0 ω.1 from rfl,
      show (taggedDriver w r ω').eta = addParticle 0 ω'.1 from rfl, hc],
    fun p s hp => ?_, fun p s hp => ?_⟩
  · show taggedMove w ω.2.1 (p, s) = taggedMove w ω'.2.1 (p, s)
    rw [taggedMove_apply, taggedMove_apply]
    by_cases h0 : p.1 = (0 : Site d)
    · rw [if_pos h0, if_pos h0]
      by_cases h2 : p.2 = 0
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        refine hm ((0, p.2 - 1), s) ?_
        have hval : (taggedDriver w r ω).eta p.1 = ω.1 (0 : Site d) + 1 := by
          show addParticle (0 : Site d) ω.1 p.1 = ω.1 (0 : Site d) + 1
          simp [addParticle, h0]
        rw [hval] at hp
        show p.2 - 1 < (ω.1 (0 : Site d)).toNat
        omega
    · rw [if_neg h0, if_neg h0]
      refine hm (p, s) ?_
      have hval : (taggedDriver w r ω).eta p.1 = ω.1 p.1 := by
        show addParticle (0 : Site d) ω.1 p.1 = ω.1 p.1
        simp only [addParticle, if_neg h0]
      rwa [hval] at hp
  · show taggedRank r ω.2.2 (p, s) = taggedRank r ω'.2.2 (p, s)
    rw [taggedRank_apply, taggedRank_apply]
    by_cases h0 : p.1 = (0 : Site d)
    · rw [if_pos h0, if_pos h0]
      by_cases h2 : p.2 = 0
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        refine hr ((0, p.2 - 1), s) ?_
        have hval : (taggedDriver w r ω).eta p.1 = ω.1 (0 : Site d) + 1 := by
          show addParticle (0 : Site d) ω.1 p.1 = ω.1 (0 : Site d) + 1
          simp [addParticle, h0]
        rw [hval] at hp
        show p.2 - 1 < (ω.1 (0 : Site d)).toNat
        omega
    · rw [if_neg h0, if_neg h0]
      refine hr (p, s) ?_
      have hval : (taggedDriver w r ω).eta p.1 = ω.1 p.1 := by
        show addParticle (0 : Site d) ω.1 p.1 = ω.1 p.1
        simp only [addParticle, if_neg h0]
      rwa [hval] at hp

/-- **`F` is symmetric in the particles present**, at the realizations whose
uniform variables are pairwise distinct. -/
theorem symmetricInParticles_survivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    SymmetricInParticles (survivalObs (d := d) w r t) := by
  classical
  intro x₀ σ ω hinj hσ
  unfold survivalObs
  have h := taggedActive_relabelAt w r hσ hinj t
  set S : Set (PData d) := {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
    with hS
  by_cases hmem : ω ∈ S
  · have h1 : relabelAt x₀ σ ω ∈ S := by
      rw [hS, Set.mem_setOf_eq, h]
      exact hmem
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem hmem]
  · have h1 : relabelAt x₀ σ ω ∉ S := by
      rw [hS, Set.mem_setOf_eq, h]
      exact hmem
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hmem]

/-- **`F` reads the particles present alone.** -/
theorem readsParticles_survivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    ReadsParticles (survivalObs (d := d) w r t) := by
  classical
  intro ω ω' _ _ hc hm hr
  unfold survivalObs
  have h : pState (taggedDriver w r ω) t = pState (taggedDriver w r ω') t :=
    pState_present (agreesOnPresent_taggedDriver w r hc hm hr) t
  set S : Set (PData d) := {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
    with hS
  by_cases hmem : ω ∈ S
  · have h1 : ω' ∈ S := by
      rw [hS, Set.mem_setOf_eq, ← h]
      exact hmem
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1]
  · have h1 : ω' ∉ S := by
      rw [hS, Set.mem_setOf_eq, ← h]
      exact hmem
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]

/-- **`F` is invariant under relabeling the particles at a site.**  This is the
hypothesis of `lem:product` for the survival observable of `thm:subcritical`. -/
theorem relabelInvariant_survivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    RelabelInvariant (survivalObs (d := d) w r t) :=
  ⟨symmetricInParticles_survivalObs w r t, readsParticles_survivalObs w r t⟩

/-- **`Z` is a function of the sites within distance `t + t(t+1)` of the
origin.** -/
theorem dependsOn_holeObs (w : ℕ → Fin d × Bool) (t : ℕ) :
    DependsOn (boxFinset (0 : Site d) (t + t * (t + 1))) (holeObs (d := d) w t) :=
  dependsOn_holeSum w t

/-- **`F` is a function of the sites within distance `t + t(t+1)` of the
origin.**  Deleting the guard is what makes this true: the guard read the
uniform variables of labels outside the box. -/
theorem dependsOn_survivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    DependsOn (boxFinset (0 : Site d) (t + t * (t + 1))) (survivalObs (d := d) w r t) := by
  classical
  intro ω ω' hc hm hr
  unfold survivalObs
  have h := taggedActive_congr w r t hc hm hr
  set S : Set (PData d) := {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
    with hS
  by_cases hmem : ω ∈ S
  · have h1 : ω' ∈ S := by
      rw [hS, Set.mem_setOf_eq, ← h]
      exact hmem
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1]
  · have h1 : ω' ∉ S := by
      rw [hS, Set.mem_setOf_eq, ← h]
      exact hmem
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]

end Parking

end
