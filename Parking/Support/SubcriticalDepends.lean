/-
The two observables of `thm:subcritical` are functions of finitely many sites.

`parking.tex:2465` says "both `F` and `Z` depend only on the finitely many sites
within distance `t` of `R_t`".  The range of the prescribed walk lies in the box
of radius `t` about the origin, and the state after `t` rounds inside a box of
radius `r` is read off the box of radius `r + t(t+1)`
(`Parking.pState_agree_box`), so the box of radius `t + t(t+1)` about the origin
carries both of them.  The radius is larger than the paper's `t` because a
particle that arrives in the range decides whether it settles by looking at the
arrivals at its own new site, a further step out at every round; only the
finiteness is used.
-/
import Parking.Support.FiniteRange
import Parking.Support.SubcriticalPair

open LatticeProb Finset

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The range of the prescribed walk lies in the box of radius `t`. -/
theorem rangeFinset_subset_box (w : ℕ → Fin d × Bool) (t : ℕ) :
    rangeFinset (0 : Site d) w t ⊆ boxFinset (0 : Site d) t := by
  intro x hx
  simp only [rangeFinset, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact walkPath_mem_box (0 : Site d) w (Nat.lt_succ_iff.mp hj)

/-- The realizations of a `DependsOn` hypothesis give agreeing drivers. -/
theorem agreesOnBox_of_depends {ρ : ℕ} {ω ω' : PData d}
    (hc : ∀ x ∈ boxFinset (0 : Site d) ρ, ω.1 x = ω'.1 x)
    (hm : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset (0 : Site d) ρ → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset (0 : Site d) ρ → ω.2.2 q = ω'.2.2 q) :
    AgreesOnBox (0 : Site d) ρ (toPDriver ω) (toPDriver ω') :=
  ⟨hc, hm, hr⟩

/-- The same for the realization with the tagged particle put back: the counts
change only at the origin, and the walks and uniform variables of a label at a
site of the box are read at a label of the same site. -/
theorem agreesOnBox_taggedDriver {ρ : ℕ} (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (h0 : (0 : Site d) ∈ boxFinset (0 : Site d) ρ) {ω ω' : PData d}
    (hc : ∀ x ∈ boxFinset (0 : Site d) ρ, ω.1 x = ω'.1 x)
    (hm : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset (0 : Site d) ρ → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset (0 : Site d) ρ → ω.2.2 q = ω'.2.2 q) :
    AgreesOnBox (0 : Site d) ρ (taggedDriver w r ω) (taggedDriver w r ω') := by
  classical
  refine ⟨fun x hx => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · show addParticle 0 ω.1 x = addParticle 0 ω'.1 x
    simp only [addParticle]
    split_ifs with hx0
    · rw [hc x hx]
    · rw [hc x hx]
  · show taggedMove w ω.2.1 q = taggedMove w ω'.2.1 q
    simp only [taggedMove]
    split_ifs with h1 h2
    · rfl
    · exact hm _ (by simpa [h1] using h0)
    · exact hm q hq
  · show taggedRank r ω.2.2 q = taggedRank r ω'.2.2 q
    simp only [taggedRank]
    split_ifs with h1 h2
    · rfl
    · exact hr _ (by simpa [h1] using h0)
    · exact hr q hq

/-- **The number of unfilled holes of the range depends on finitely many
sites.** -/
theorem dependsOn_holeSum (w : ℕ → Fin d × Bool) (t : ℕ) :
    DependsOn (boxFinset (0 : Site d) (t + t * (t + 1)))
      (fun ω : PData d =>
        ∑ x ∈ rangeFinset (0 : Site d) w t, (pHoleCount (toPDriver ω) t x : ℝ)) := by
  intro ω ω' hc hm hr
  have hagree := agreesOnBox_of_depends hc hm hr
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x ∈ boxFinset (0 : Site d) t := rangeFinset_subset_box w t hx
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
    (pHoleCount_congr_box hagree (le_refl (t + t * (t + 1))) hx')

/-- **The activity of the tagged particle depends on finitely many sites.** -/
theorem taggedActive_congr (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (t : ℕ) {ω ω' : PData d}
    (hc : ∀ x ∈ boxFinset (0 : Site d) (t + t * (t + 1)), ω.1 x = ω'.1 x)
    (hm : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset (0 : Site d) (t + t * (t + 1)) →
      ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.1 ∈ boxFinset (0 : Site d) (t + t * (t + 1)) →
      ω.2.2 q = ω'.2.2 q) :
    (pState (taggedDriver w rk ω) t).active (0, 0)
      = (pState (taggedDriver w rk ω') t).active (0, 0) := by
  have h0 : (0 : Site d) ∈ boxFinset (0 : Site d) (t + t * (t + 1)) :=
    mem_boxFinset_iff.mpr fun i => by simp; positivity
  have hagree := agreesOnBox_taggedDriver w rk h0 hc hm hr
  have hzero : ((0 : Label d)).1 ∈ boxFinset (0 : Site d) t :=
    mem_boxFinset_iff.mpr fun i => by simp
  exact pState_active_congr_box hagree (r := t) (le_refl (t + t * (t + 1))) hzero

end Parking

end
