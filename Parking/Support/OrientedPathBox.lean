/- The directed walk stays in the box of radius `j`, and its indicator
decomposition over the fibres of the box. -/
import Parking.Support.OrientedMaximum
import Parking.Support.Pathwise
import Parking.Support.Walk
import Parking.Support.Coupling
import Parking.Support.WStarMoment
import Parking.Support.OrientedIncrement

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The directed walk after `j` steps stays in the box of radius `j`. -/
theorem orientedPath_mem_box (x : Site d) (p : ℕ → Fin d × Bool) {j n : ℕ} (hj : j ≤ n) :
    orientedPath x p j ∈ boxFinset x n := by
  rw [LatticeProb.mem_boxFinset_iff]
  intro i
  have h : ∀ k : ℕ, |orientedPath x p k i - x i| ≤ (k : ℤ) := by
    intro k
    induction k with
    | zero => simp [orientedPath]
    | succ k ih =>
      have h1 : |orientedPath x p (k + 1) i - orientedPath x p k i| ≤ 1 := by
        have hdiff : orientedPath x p (k + 1) i - orientedPath x p k i = -(unit (p k).1) i := by
          simp [orientedPath, Pi.sub_apply]
        rw [hdiff, abs_neg]
        by_cases hc : i = (p k).1 <;> simp [unit, hc]
      calc |orientedPath x p (k + 1) i - x i|
          = |(orientedPath x p (k + 1) i - orientedPath x p k i)
              + (orientedPath x p k i - x i)| := by congr 1; ring
        _ ≤ |orientedPath x p (k + 1) i - orientedPath x p k i|
              + |orientedPath x p k i - x i| := abs_add_le _ _
        _ ≤ 1 + (k : ℤ) := by linarith
        _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  exact le_trans (h j) (by exact_mod_cast hj)

/-- The directed walk indicator decomposition over the fibres of the box. -/
theorem orientedPath_indicator_sum (j : ℕ) (f : Site d → ℝ) (p : ℕ → Fin d × Bool) :
    f (orientedPath (0 : Site d) p j)
      = ∑ z ∈ boxFinset (0 : Site d) j,
          Set.indicator {q | orientedPath (0 : Site d) q j = z} (fun _ => f z) p := by
  classical
  have hmem : orientedPath (0 : Site d) p j ∈ boxFinset (0 : Site d) j :=
    orientedPath_mem_box 0 p (le_refl j)
  have hterm : ∀ z ∈ boxFinset (0 : Site d) j,
      Set.indicator {q | orientedPath (0 : Site d) q j = z} (fun _ => f z) p
        = if orientedPath (0 : Site d) p j = z then f z else 0 := by
    intro z _
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq (boxFinset (0 : Site d) j) (orientedPath (0 : Site d) p j) f, if_pos hmem]

/-- The directed walk fibre is measurable. -/
theorem measurableSet_orientedPath_fibre (j : ℕ) (z : Site d) :
    MeasurableSet {p : ℕ → Fin d × Bool | orientedPath (0 : Site d) p j = z} :=
  (measurable_orientedPath (0 : Site d) j) (measurableSet_singleton z)

/-- The average over the directed walk of a function of its position is the
finite combination over the fibres of the box. -/
theorem integral_orientedPath_decomp (hd : 1 ≤ d) (j : ℕ) (f : Site d → ℝ) :
    ∫ p, f (orientedPath (0 : Site d) p j) ∂(walkLaw d)
      = ∑ z ∈ boxFinset (0 : Site d) j,
          (walkLaw d).real {p | orientedPath (0 : Site d) p j = z} * f z := by
  classical
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  rw [integral_congr_ae (Filter.Eventually.of_forall (orientedPath_indicator_sum j f)),
    integral_finsetSum _ fun z _ =>
      (integrable_const (f z)).indicator (measurableSet_orientedPath_fibre j z)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_indicator_const (f z) (measurableSet_orientedPath_fibre j z), smul_eq_mul]

end Parking
end
