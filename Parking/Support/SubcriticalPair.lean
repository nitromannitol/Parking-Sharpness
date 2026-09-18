/-
The pair `(F, Z)` of the proof of `thm:subcritical` (`parking.tex:2434-2447`).

"Prescribe the `k` particles at the origin and temporarily condition on all
their walks and uniform variables.  Remove particle 1, and let `Z` be the number
of unfilled holes in `R_t` at time `t` in the resulting process.  Let `F`
indicate that particle 1 has not settled by time `t` when it is put back."

So `Z` is read off the realization `ω` itself, whose origin carries the `k - 1`
remaining particles, and `F` is read off `taggedDriver w r ω`, which puts the
prescribed particle back at the origin as the label `(0, 0)` and pushes the
labels of the particles already there up by one.  Writing the tagged particle at
the BOTTOM label rather than the top is what makes

  `taggedDriver w r (addAt x₀ ω) = addParticleDriver x₀ (taggedDriver w r ω)`

an identity of drivers for every site `x₀`, so that the monotonicity of `F`
under adding a particle is exactly `lem:tagged-monotonicity`.

Neither observable carries a guard.  The relabeling clauses of `lem:product` are
asked for at the realizations whose uniform variables are pairwise distinct, and
there the hole counts are equivariant outright, while the tagged dynamics is
equivariant because every tie in the tagged driver involves the tagged label and
one other, and the site-major label order decides such a tie by data a
relabeling of the particles present at a site never moves
(`Support/SubcriticalRelabel.lean`).
-/
import Parking.Support.RelabelEquiv
import Parking.Support.ReadsPresent
import Parking.Support.DeleteCompare
import Parking.Frozen.OneParticle
import Parking.Frozen.TaggedMonotonicity

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- `R_t`, the range of the prescribed walk from the origin, as a finset. -/
def rangeFinset (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) : Finset (Site d) :=
  (Finset.range (t + 1)).image fun j => walkPath x p j

theorem rangeCard_eq_card (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    rangeCard x p t = (rangeFinset x p t).card := rfl

/-- The walks after the tagged particle is put back at the origin as the label
`(0, 0)`: the labels already at the origin move up by one. -/
def taggedMove (w : ℕ → Fin d × Bool) (m : Label d × ℕ → Fin d × Bool) :
    Label d × ℕ → Fin d × Bool :=
  fun q => if q.1.1 = 0 then (if q.1.2 = 0 then w q.2 else m ((0, q.1.2 - 1), q.2)) else m q

/-- The uniform variables after the tagged particle is put back. -/
def taggedRank (r : ℕ → ℝ) (v : Label d × ℕ → ℝ) : Label d × ℕ → ℝ :=
  fun q => if q.1.1 = 0 then (if q.1.2 = 0 then r q.2 else v ((0, q.1.2 - 1), q.2)) else v q

/-- The realization with the prescribed particle put back at the origin. -/
def taggedDriver (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (ω : PData d) : PDriver d :=
  ⟨addParticle 0 ω.1, taggedMove w ω.2.1, taggedRank r ω.2.2⟩

/-- Adding a particle commutes with putting the tagged particle back. -/
theorem taggedDriver_addAt (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (x₀ : Site d) (ω : PData d) :
    taggedDriver w r (addAt x₀ ω) = addParticleDriver x₀ (taggedDriver w r ω) := by
  have heta : addParticle 0 (addParticle x₀ ω.1) = addParticle x₀ (addParticle 0 ω.1) := by
    funext x
    simp only [addParticle]
    split_ifs <;> try rfl
  exact congrArg (fun e => PDriver.mk e (taggedMove w ω.2.1) (taggedRank r ω.2.2)) heta

/-- `F`, the indicator that the tagged particle has not settled by time `t`. -/
def survivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) : PData d → ℝ :=
  Set.indicator {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
    (fun _ => 1)

/-- `Z`, the number of unfilled holes of `R_t` at time `t` once the tagged
particle is removed. -/
def holeObs (w : ℕ → Fin d × Bool) (t : ℕ) : PData d → ℝ :=
  fun ω => ∑ x ∈ rangeFinset (0 : Site d) w t, (pHoleCount (toPDriver ω) t x : ℝ)

/-- `F` takes values in `[0, 1]`. -/
theorem survivalObs_mem_Icc (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) (ω : PData d) :
    survivalObs w r t ω ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold survivalObs
  by_cases h : ω ∈ {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
  · rw [Set.indicator_of_mem h]; exact ⟨zero_le_one, le_refl 1⟩
  · rw [Set.indicator_of_notMem h]; exact ⟨le_refl 0, zero_le_one⟩

/-- `Z` is nonnegative. -/
theorem holeObs_nonneg (w : ℕ → Fin d × Bool) (t : ℕ) (ω : PData d) :
    0 ≤ holeObs w t ω :=
  Finset.sum_nonneg fun x _ => by positivity

/-- **`Z` is symmetric in the particles present**, at the realizations whose
uniform variables are pairwise distinct: the hole counts of the relabelled
realization are those of the original one. -/
theorem symmetricInParticles_holeObs (w : ℕ → Fin d × Bool) (t : ℕ) :
    SymmetricInParticles (holeObs (d := d) w t) := by
  intro x₀ σ ω hinj hσ
  refine Finset.sum_congr rfl fun x _ => ?_
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (pHoleCount_relabelAt hσ hinj t x)

/-- **`Z` reads the particles present alone.** -/
theorem readsParticles_holeObs (w : ℕ → Fin d × Bool) (t : ℕ) :
    ReadsParticles (holeObs (d := d) w t) := by
  intro ω ω' _ _ hc hm hr
  refine Finset.sum_congr rfl fun x _ => ?_
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (pHoleCount_reads hc hm hr t x)

/-- **`Z` is invariant under relabeling the particles at a site.** -/
theorem relabelInvariant_holeObs (w : ℕ → Fin d × Bool) (t : ℕ) :
    RelabelInvariant (holeObs (d := d) w t) :=
  ⟨symmetricInParticles_holeObs w t, readsParticles_holeObs w t⟩



/-- Adding a particle does not create a hole. -/
theorem pHoleCount_addParticleDriver_le (hd : 1 ≤ d) (D : PDriver d) (x₀ : Site d)
    (t : ℕ) (x : Site d) :
    pHoleCount (addParticleDriver x₀ D) t x ≤ pHoleCount D t x := by
  rcases Frozen.one_particle d hd D x₀ t with ⟨h1, -⟩ | ⟨-, z, hz, hz'⟩
  · exact le_of_eq (h1 x)
  · by_cases hx : x = z
    · subst hx; omega
    · exact le_of_eq (hz' x hx).symm

/-- **`F` does not decrease when a particle is added.**  This is
`lem:tagged-monotonicity` read through `taggedDriver_addAt`. -/
theorem survivalObs_mono (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    survivalObs w r t ω ≤ survivalObs w r t (addAt x₀ ω) := by
  classical
  unfold survivalObs
  by_cases h : ω ∈ {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
  · have h2 : addAt x₀ ω ∈
        {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true} := by
      show (pState (taggedDriver w r (addAt x₀ ω)) t).active (0, 0) = true
      rw [taggedDriver_addAt]
      exact Frozen.tagged_monotonicity d hd (taggedDriver w r ω) x₀ t (0, 0) h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h2]
  · rw [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **`Z` does not increase when a particle is added.** -/
theorem holeObs_anti (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    holeObs w t (addAt x₀ ω) ≤ holeObs w t ω := by
  refine Finset.sum_le_sum fun x _ => ?_
  exact_mod_cast pHoleCount_addParticleDriver_le hd (toPDriver ω) x₀ t x

/-- **Adding a particle changes `Z` by at most one.**  By `lem:one-particle` the
hole counts either all stay put or exactly one of them drops by one. -/
theorem holeObs_add_lip (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    |holeObs w t (addAt x₀ ω) - holeObs w t ω| ≤ 1 := by
  classical
  have hdef : toPDriver (addAt x₀ ω) = addParticleDriver x₀ (toPDriver ω) := rfl
  unfold holeObs
  rcases Frozen.one_particle d hd (toPDriver ω) x₀ t with ⟨h1, -⟩ | ⟨-, z, hz, hz'⟩
  · have hcong : ∀ x ∈ rangeFinset (0 : Site d) w t,
        ((pHoleCount (toPDriver (addAt x₀ ω)) t x : ℕ) : ℝ)
          = ((pHoleCount (toPDriver ω) t x : ℕ) : ℝ) := by
      intro x _
      rw [hdef, h1 x]
    rw [Finset.sum_congr rfl hcong, sub_self, abs_zero]
    exact zero_le_one
  · have key : ∀ x ∈ rangeFinset (0 : Site d) w t,
        ((pHoleCount (toPDriver ω) t x : ℕ) : ℝ)
            - ((pHoleCount (toPDriver (addAt x₀ ω)) t x : ℕ) : ℝ)
          = if x = z then 1 else 0 := by
      intro x _
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl, hdef, hz]
        push_cast
        ring
      · rw [if_neg hx, hdef, hz' x hx, sub_self]
    have hs : (∑ x ∈ rangeFinset (0 : Site d) w t,
            ((pHoleCount (toPDriver ω) t x : ℕ) : ℝ))
          - ∑ x ∈ rangeFinset (0 : Site d) w t,
            ((pHoleCount (toPDriver (addAt x₀ ω)) t x : ℕ) : ℝ)
        = if z ∈ rangeFinset (0 : Site d) w t then 1 else 0 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl key]
      exact Finset.sum_ite_eq' (rangeFinset (0 : Site d) w t) z fun _ => (1 : ℝ)
    by_cases hzR : z ∈ rangeFinset (0 : Site d) w t
    · rw [if_pos hzR] at hs
      rw [abs_le]
      constructor <;> linarith
    · rw [if_neg hzR] at hs
      rw [abs_le]
      constructor <;> linarith

/-- **Deleting a particle changes `Z` by at most one**, because deleting is the
inverse of adding. -/
theorem holeObs_del_lip (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    |holeObs w t (delAt x₀ ω) - holeObs w t ω| ≤ 1 := by
  have h := holeObs_add_lip hd w t x₀ (delAt x₀ ω)
  rw [addAt_delAt] at h
  rw [abs_sub_comm]
  exact h

end Parking

end
