import Parking.Support.WalkShiftInvariance
import LatticeProb.Prob.MapPi

/-!
# Coordinate reflections of the parking walk

The symmetric step law is invariant under reversing the signs of any chosen
set of coordinate directions.
-/

noncomputable section

open MeasureTheory

namespace Parking

variable {d : ℕ}

/-- Reverse the signs in a selected set of coordinate directions. -/
def reflectDirection (s : Fin d → Bool) (b : Fin d × Bool) : Fin d × Bool :=
  (b.1, if s b.1 then !b.2 else b.2)

/-- Reflecting the same set of coordinates twice returns the direction. -/
theorem reflectDirection_involutive (s : Fin d → Bool) :
    Function.Involutive (reflectDirection s) := by
  rintro ⟨i, b⟩
  cases h : s i <;> cases b <;> simp [reflectDirection, h]

/-- The uniform signed-direction law is invariant under coordinate reflection. -/
theorem map_stepLaw_reflectDirection (s : Fin d → Bool) :
    (stepLaw d).map (reflectDirection s) = stepLaw d := by
  have hm : Measurable (reflectDirection s) := measurable_of_countable _
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply hm (MeasurableSet.singleton b)]
  have hpre : (reflectDirection s) ⁻¹' {b} = {reflectDirection s b} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, reflectDirection_involutive]
    · intro h
      rw [h, reflectDirection_involutive]
  rw [hpre]
  simp [stepLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply']

/-- Reflecting each step of a direction sequence preserves its law. -/
theorem measurePreserving_reflectDirections (hd : 1 ≤ d) (s : Fin d → Bool) :
    MeasurePreserving (fun p : ℕ → Fin d × Bool => fun n => reflectDirection s (p n))
      (walkLaw d) (walkLaw d) := by
  have := stepLaw_isProbability hd
  refine ⟨Measurable.of_eval fun n => (measurable_of_countable (reflectDirection s)).comp
    (measurable_pi_apply n), ?_⟩
  rw [walkLaw, LatticeProb.infinitePi_map_pi (stepLaw d)
    (measurable_of_countable (reflectDirection s)), map_stepLaw_reflectDirection]

/-- Reflect the selected coordinates of a lattice site. -/
def reflectSite (s : Fin d → Bool) (x : Site d) : Site d :=
  fun i => if s i then -x i else x i

/-- Coordinate reflection preserves the graph norm. -/
theorem graphNorm_reflectSite (s : Fin d → Bool) (x : Site d) :
    graphNorm (reflectSite s x) = graphNorm x := by
  unfold graphNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [reflectSite, h]

/-- Reflection is compatible with addition of lattice sites. -/
theorem reflectSite_add (s : Fin d → Bool) (x y : Site d) :
    reflectSite s (x + y) = reflectSite s x + reflectSite s y := by
  ext i
  cases h : s i <;> simp [reflectSite, h, add_comm]

/-- A reflected signed direction produces the reflected displacement. -/
theorem stepVec_reflectDirection (s : Fin d → Bool) (b : Fin d × Bool) :
    stepVec (reflectDirection s b) = reflectSite s (stepVec b) := by
  obtain ⟨i, b⟩ := b
  ext j
  by_cases h : j = i
  · subst j
    cases hs : s i <;> cases b <;>
      simp [stepVec, reflectDirection, reflectSite, LatticeProb.unit, hs]
  · cases hs : s i <;> cases ht : s j <;> cases b <;>
      simp [stepVec, reflectDirection, reflectSite, LatticeProb.unit, hs, ht, h]

/-- Reflecting each step reflects the walk started at the origin. -/
theorem walkPath_reflectDirections (s : Fin d → Bool) (p : ℕ → Fin d × Bool) (n : ℕ) :
    walkPath (0 : Site d) (fun k => reflectDirection s (p k)) n =
      reflectSite s (walkPath (0 : Site d) p n) := by
  induction n with
  | zero =>
      ext i
      simp [walkPath, reflectSite]
  | succ n ih =>
      rw [walkPath, ih, stepVec_reflectDirection, ← reflectSite_add, ← walkPath]

end Parking

end
