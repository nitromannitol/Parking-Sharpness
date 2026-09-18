/-
`F Z = 0` for the paper's `Z` (`parking.tex:2448-2452`).

"On `{F = 1}`, particle 1 fills no hole, so removing it does not change the holes
through time `t`.  Every hole at a site it visits is filled by the end of that
round.  Thus no site of `R_t` carries an unfilled hole at time `t`, and `FZ = 0`."

`Parking.taggedDriver_holeCount_range` is the second sentence, computed in the
realization that carries the tagged particle.  The first sentence is the passage
from that realization to `ω`, which carries the other particles alone, and it
goes in three steps.  The tagged particle sits at the BOTTOM label of the origin
in `taggedDriver`, so relabel the origin by the cycle that carries it to the TOP
label; the realization with the tagged particle on top is `addAt 0` of a
realization whose particles present are exactly those of `ω`; and adding a
particle that is still active changes no hole count.  The relabeling is the only
step that reads the uniform variables, and it asks for the pairwise distinctness
of the ones the tagged realization carries, which holds almost surely.
-/
import Parking.Support.TaggedSurvivor

open LatticeProb Finset

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The realization with the tagged particle put back, as driving data. -/
def taggedData (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) : PData d :=
  (addParticle 0 ω.1, taggedMove w ω.2.1, taggedRank rk ω.2.2)

theorem taggedDriver_eq_toPDriver (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) :
    taggedDriver w rk ω = toPDriver (taggedData w rk ω) := rfl

/-- The origin's bottom label goes to the label `c`, and `0, …, c - 1` move up
by one. -/
def liftUp (c i : ℕ) : ℕ := if i < c then i + 1 else if i = c then 0 else i

/-- The inverse of `Parking.liftUp`. -/
def liftDown (c j : ℕ) : ℕ := if j = 0 then c else if j ≤ c then j - 1 else j

theorem liftDown_liftUp (c i : ℕ) : liftDown c (liftUp c i) = i := by
  unfold liftUp liftDown
  by_cases h1 : i < c
  · rw [if_pos h1, if_neg (show ¬ (i + 1 = 0) by omega), if_pos (show i + 1 ≤ c by omega)]
    omega
  · by_cases h2 : i = c
    · rw [if_neg h1, if_pos h2, if_pos rfl]
      omega
    · rw [if_neg h1, if_neg h2, if_neg (show ¬ (i = 0) by omega),
        if_neg (show ¬ (i ≤ c) by omega)]

theorem liftUp_liftDown (c j : ℕ) : liftUp c (liftDown c j) = j := by
  unfold liftUp liftDown
  by_cases h1 : j = 0
  · rw [if_pos h1, if_neg (show ¬ (c < c) by omega), if_pos rfl]
    omega
  · by_cases h2 : j ≤ c
    · rw [if_neg h1, if_pos h2, if_pos (show j - 1 < c by omega)]
      omega
    · rw [if_neg h1, if_neg h2, if_neg (show ¬ (j < c) by omega),
        if_neg (show ¬ (j = c) by omega)]

/-- The cycle that carries the bottom label of the origin to the label `c`,
pushing `0, …, c - 1` up by one, and fixes every index above `c`. -/
def liftCycle (c : ℕ) : Equiv.Perm ℕ :=
  ⟨liftUp c, liftDown c, liftDown_liftUp c, liftUp_liftDown c⟩

theorem liftCycle_apply (c i : ℕ) : liftCycle c i = liftUp c i := rfl

theorem liftCycle_fixes (c : ℕ) : ∀ i, c + 1 ≤ i → liftCycle c i = i := by
  intro i hi
  rw [liftCycle_apply, liftUp, if_neg (show ¬ (i < c) by omega),
    if_neg (show ¬ (i = c) by omega)]

/-- The realization with the tagged particle carried to the TOP label of the
origin, so that the labels below it are exactly the particles of `ω`. -/
def swapData (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) : PData d :=
  relabelAt 0 (liftCycle (ω.1 0).toNat) (taggedData w rk ω)

theorem swapData_fst (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) :
    (swapData w rk ω).1 = addParticle 0 ω.1 := rfl

theorem delAt_swapData_fst (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) :
    (delAt 0 (swapData w rk ω)).1 = ω.1 := by
  funext x
  show (if x = 0 then (addParticle 0 ω.1) x - 1 else (addParticle 0 ω.1) x) = ω.1 x
  by_cases hx : x = 0
  · rw [if_pos hx, hx]
    simp [addParticle]
  · rw [if_neg hx]
    simp only [addParticle, if_neg hx]

theorem liftCycle_fixes_taggedData (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d)
    (hη : (0 : ℤ) ≤ ω.1 0) :
    ∀ i, ((taggedData w rk ω).1 0).toNat ≤ i → liftCycle (ω.1 0).toNat i = i := by
  intro i hi
  refine liftCycle_fixes _ i ?_
  have hval : ((taggedData w rk ω).1 0) = ω.1 0 + 1 := by
    show (addParticle 0 ω.1) 0 = ω.1 0 + 1
    simp [addParticle]
  rw [hval] at hi
  omega

/-- The tagged particle is the top label of the origin in the swapped
realization. -/
theorem swapData_active (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) {t : ℕ}
    (hη : (0 : ℤ) ≤ ω.1 0) (hinj : Function.Injective (taggedRank rk ω.2.2))
    (h : (pState (taggedDriver w rk ω) t).active (0, 0) = true) :
    (pState (toPDriver (swapData w rk ω)) t).active (0, (ω.1 0).toNat) = true := by
  have hkey := pState_active_relabelAt (x₀ := (0 : Site d))
    (σ := liftCycle (ω.1 0).toNat) (ω := taggedData w rk ω)
    (liftCycle_fixes_taggedData w rk ω hη) hinj t (0, (ω.1 0).toNat)
  have hperm : permLabel (0 : Site d) (liftCycle (ω.1 0).toNat) (0, (ω.1 0).toNat)
      = ((0 : Site d), 0) := by
    have : liftCycle (ω.1 0).toNat (ω.1 0).toNat = 0 := by
      rw [liftCycle_apply, liftUp, if_neg (lt_irrefl _), if_pos rfl]
    simp only [permLabel, this, if_true]
  rw [swapData, hkey, hperm]
  exact h

/-- The swapped realization and `ω` carry the same particles once the tagged one
is deleted. -/
theorem holeCount_delAt_swapData (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d)
    (t : ℕ) (x : Site d) :
    pHoleCount (toPDriver (delAt 0 (swapData w rk ω))) t x = pHoleCount (toPDriver ω) t x := by
  refine pHoleCount_reads (delAt_swapData_fst w rk ω) ?_ ?_ t x
  · intro q hq
    rw [delAt_swapData_fst w rk ω] at hq
    show taggedMove w ω.2.1
        ((q.1.1, if q.1.1 = 0 then liftCycle (ω.1 0).toNat q.1.2 else q.1.2), q.2) = ω.2.1 q
    by_cases hx : q.1.1 = (0 : Site d)
    · rw [if_pos hx]
      have hlt : q.1.2 < (ω.1 0).toNat := by rwa [hx] at hq
      have hup : liftCycle (ω.1 0).toNat q.1.2 = q.1.2 + 1 := by
        rw [liftCycle_apply, liftUp, if_pos hlt]
      rw [hup]
      simp only [taggedMove, if_pos hx, if_neg (Nat.succ_ne_zero q.1.2)]
      simp only [Nat.add_sub_cancel, ← hx]
    · rw [if_neg hx]
      simp only [taggedMove, if_neg hx]
  · intro q hq
    rw [delAt_swapData_fst w rk ω] at hq
    show taggedRank rk ω.2.2
        ((q.1.1, if q.1.1 = 0 then liftCycle (ω.1 0).toNat q.1.2 else q.1.2), q.2) = ω.2.2 q
    by_cases hx : q.1.1 = (0 : Site d)
    · rw [if_pos hx]
      have hlt : q.1.2 < (ω.1 0).toNat := by rwa [hx] at hq
      have hup : liftCycle (ω.1 0).toNat q.1.2 = q.1.2 + 1 := by
        rw [liftCycle_apply, liftUp, if_pos hlt]
      rw [hup]
      simp only [taggedRank, if_pos hx, if_neg (Nat.succ_ne_zero q.1.2)]
      simp only [Nat.add_sub_cancel, ← hx]
    · rw [if_neg hx]
      simp only [taggedRank, if_neg hx]

/-- **`F Z = 0`**: once the tagged particle has survived to time `t`, no site of
its range carries an unfilled hole in the realization that carries the other
particles alone. -/
theorem holeCount_range_of_survival (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (ω : PData d) {t : ℕ}
    (hη : (0 : ℤ) ≤ ω.1 0) (hinj : Function.Injective (taggedRank rk ω.2.2))
    (h : (pState (taggedDriver w rk ω) t).active (0, 0) = true) :
    ∀ x ∈ rangeFinset (0 : Site d) w t, pHoleCount (toPDriver ω) t x = 0 := by
  intro x hx
  have hswap : toPDriver (swapData w rk ω)
      = addParticleDriver 0 (toPDriver (delAt 0 (swapData w rk ω))) := by
    rw [show addParticleDriver (0 : Site d) (toPDriver (delAt 0 (swapData w rk ω)))
        = toPDriver (addAt 0 (delAt 0 (swapData w rk ω))) from rfl, addAt_delAt]
  have hcount : ((toPDriver (delAt 0 (swapData w rk ω))).eta 0).toNat = (ω.1 0).toNat := by
    show ((delAt 0 (swapData w rk ω)).1 0).toNat = (ω.1 0).toNat
    rw [delAt_swapData_fst w rk ω]
  have hact : (pState (addParticleDriver 0 (toPDriver (delAt 0 (swapData w rk ω)))) t).active
      (0, ((toPDriver (delAt 0 (swapData w rk ω))).eta 0).toNat) = true := by
    rw [← hswap, hcount]
    exact swapData_active w rk ω hη hinj h
  have h1 : pHoleCount (toPDriver (swapData w rk ω)) t x
      = pHoleCount (toPDriver (delAt 0 (swapData w rk ω))) t x := by
    rw [hswap]
    exact pHoleCount_addParticleDriver_eq_of_active _ 0 t hact x
  have h2 : pHoleCount (toPDriver (swapData w rk ω)) t x
      = pHoleCount (taggedDriver w rk ω) t x :=
    pHoleCount_relabelAt (liftCycle_fixes_taggedData w rk ω hη) hinj t x
  have h3 : pHoleCount (taggedDriver w rk ω) t x = 0 :=
    taggedDriver_holeCount_range w rk ω hη h x hx
  rw [← holeCount_delAt_swapData w rk ω t x, ← h1, h2, h3]

/-- **`F Z = 0`, Step 1 of `thm:subcritical`** (`parking.tex:2448-2452`), for the
two observables of `Support/SubcriticalPair.lean`, at every realization whose
origin carries the prescribed particles. -/
theorem survivalObs_mul_holeObs (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (t : ℕ) (ω : PData d)
    (hη : (0 : ℤ) ≤ ω.1 0) (hinj : Function.Injective (taggedRank rk ω.2.2)) :
    survivalObs w rk t ω * holeObs w t ω = 0 := by
  classical
  by_cases hmem : ω ∈ {ω : PData d | (pState (taggedDriver w rk ω) t).active (0, 0) = true}
  · have hz : holeObs w t ω = 0 := by
      unfold holeObs
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [holeCount_range_of_survival w rk ω hη hinj hmem x hx]
      simp
    rw [hz, mul_zero]
  · unfold survivalObs
    rw [Set.indicator_of_notMem hmem, zero_mul]

end Parking

end
