/-
Measurability of the pair `(F, Z)` of the proof of `thm:subcritical`.

`lem:product` asks that both observables be measurable, which is what
"functions of the counts, walks, and uniform variables at these sites"
(`parking.tex:2321-2332`) asserts of them.  The state of the particle-driven
construction is a measurable function of its driving data
(`Parking.measurableState_pState`), and the guard both observables carry is the
set where a measurable family of uniform variables is injective, a countable
intersection of the complements of the sets where two of them agree.
-/
import Parking.Support.Matched
import Parking.Support.SubcriticalPair

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The set where a measurable family of uniform variables is injective is
measurable.** -/
theorem measurableSet_injective_rank {v : PData d → (Label d × ℕ → ℝ)} (hv : Measurable v) :
    MeasurableSet {ω : PData d | Function.Injective (v ω)} := by
  classical
  have hcoord : ∀ q : Label d × ℕ, Measurable fun ω : PData d => v ω q := fun q =>
    (measurable_pi_apply q).comp hv
  have hset : {ω : PData d | Function.Injective (v ω)}
      = ⋂ q : Label d × ℕ, ⋂ q' : Label d × ℕ, {ω : PData d | v ω q = v ω q' → q = q'} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.Injective]
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => ?_
  by_cases hqq : q = q'
  · have huniv : {ω : PData d | v ω q = v ω q' → q = q'} = Set.univ := by
      ext ω; simp [hqq]
    rw [huniv]; exact MeasurableSet.univ
  · have heq : {ω : PData d | v ω q = v ω q' → q = q'}
        = {ω : PData d | v ω q = v ω q'}ᶜ := by
      ext ω; simp [hqq]
    rw [heq]
    exact (measurableSet_eq_fun (hcoord q) (hcoord q')).compl

/-- The number of unfilled holes of the range is a measurable function of the
driving data. -/
theorem measurable_holeSum (w : ℕ → Fin d × Bool) (t : ℕ) :
    Measurable fun ω : PData d =>
      ∑ x ∈ rangeFinset (0 : Site d) w t, (pHoleCount (toPDriver ω) t x : ℝ) := by
  have hst := Parking.measurableState_pState (Ω := PData d)
    (fun ω : PData d => ω.1) (fun ω : PData d => ω.2.1) (fun ω : PData d => ω.2.2)
    measurable_fst (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd) t
  refine Finset.measurable_sum _ fun x _ => ?_
  exact measurable_from_top.comp (hst.2.2.1 x)

/-- The counts with the tagged particle put back are measurable. -/
theorem measurable_addParticle_fst (x₀ : Site d) :
    Measurable fun ω : PData d => addParticle x₀ ω.1 := by
  classical
  refine measurable_pi_lambda _ fun x => ?_
  by_cases h : x = x₀
  · simp only [addParticle, if_pos h]
    exact ((measurable_pi_apply x).comp measurable_fst).add_const 1
  · simp only [addParticle, if_neg h]
    exact (measurable_pi_apply x).comp measurable_fst

/-- The walks with the tagged particle put back are measurable. -/
theorem measurable_taggedMove (w : ℕ → Fin d × Bool) :
    Measurable fun ω : PData d => taggedMove w ω.2.1 := by
  classical
  refine measurable_pi_lambda _ fun q => ?_
  by_cases h : q.1.1 = (0 : Site d)
  · by_cases h2 : q.1.2 = 0
    · simp only [taggedMove, if_pos h, if_pos h2]
      exact measurable_const
    · simp only [taggedMove, if_pos h, if_neg h2]
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  · simp only [taggedMove, if_neg h]
    exact (measurable_pi_apply q).comp (measurable_fst.comp measurable_snd)

/-- The uniform variables with the tagged particle put back are measurable. -/
theorem measurable_taggedRank (r : ℕ → ℝ) :
    Measurable fun ω : PData d => taggedRank r ω.2.2 := by
  classical
  refine measurable_pi_lambda _ fun q => ?_
  by_cases h : q.1.1 = (0 : Site d)
  · by_cases h2 : q.1.2 = 0
    · simp only [taggedRank, if_pos h, if_pos h2]
      exact measurable_const
    · simp only [taggedRank, if_pos h, if_neg h2]
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
  · simp only [taggedRank, if_neg h]
    exact (measurable_pi_apply q).comp (measurable_snd.comp measurable_snd)

/-- Every field of the state with the tagged particle put back is measurable. -/
theorem measurableState_taggedDriver (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    Parking.MeasurableState (fun ω : PData d => pState (taggedDriver w r ω) t) :=
  Parking.measurableState_pState (Ω := PData d)
    (fun ω : PData d => addParticle 0 ω.1) (fun ω : PData d => taggedMove w ω.2.1)
    (fun ω : PData d => taggedRank r ω.2.2)
    (measurable_addParticle_fst 0) (measurable_taggedMove w) (measurable_taggedRank r) t

/-- **`Z` is measurable.** -/
theorem measurable_holeObs (w : ℕ → Fin d × Bool) (t : ℕ) : Measurable (holeObs w t) :=
  measurable_holeSum w t

/-- **`F` is measurable.** -/
theorem measurable_survivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    Measurable (survivalObs w r t) := by
  classical
  have h2 : MeasurableSet
      {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true} :=
    (measurableState_taggedDriver w r t).1 (0, 0) (measurableSet_singleton true)
  exact measurable_const.indicator h2

end Parking

end
