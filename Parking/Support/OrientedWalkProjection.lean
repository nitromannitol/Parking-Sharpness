import Parking.Support.TightHappExact
import Sandpile.Walk
import Mathlib.Probability.Independence.InfinitePi

/-!
# Projection of the oriented walk

The difference between the two coordinates of the oriented walk is a
one-dimensional simple random walk. The projected path has the same law as
the walk used in the sandpile stopping problem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Parking

/-- The signed increment in the coordinate difference `z 0 - z 1`. -/
def orientedProjectedStep (b : Fin 2 × Bool) : Sandpile.Site 1 :=
  if b.1 = 0 then -LatticeProb.unit 0 else LatticeProb.unit 0

/-- The path of coordinate differences of an oriented walk. -/
def orientedProjectedPath (p : ℕ → Fin 2 × Bool) (k : ℕ) : Sandpile.Site 1 :=
  fun _ => orientedPath (0 : Site 2) p k 0 - orientedPath (0 : Site 2) p k 1

/-- The projected path is the sum of the projected increments. -/
theorem orientedProjectedPath_eq_walkPath (p : ℕ → Fin 2 × Bool) :
    orientedProjectedPath p = Sandpile.walkPath 0 (fun j => orientedProjectedStep (p j)) := by
  funext k
  induction k with
  | zero => ext i; simp [orientedProjectedPath, orientedPath, Sandpile.walkPath]
  | succ k ih =>
    ext i
    have hi := congrFun ih i
    simp only [orientedProjectedPath, orientedPath, Pi.sub_apply] at hi ⊢
    simp only [Sandpile.walkPath, Finset.sum_range_succ, Pi.add_apply, Pi.zero_apply] at hi ⊢
    fin_cases i
    rcases p k with ⟨c, b⟩
    fin_cases c <;> simp [orientedProjectedStep, LatticeProb.unit] at * <;> omega

/-- The scaled oriented site is the projected position multiplied by the
    inverse spatial scaling. -/
theorem orientedScaledSite_eq_projectedPath (n k : ℕ) (p : ℕ → Fin 2 × Bool) :
    orientedScaledSite n (orientedPath (0 : Site 2) p k) =
      -((orientedProjectedPath p k 0 : ℤ) : ℝ) / (2 * Real.sqrt n) := by
  simp only [orientedScaledSite, orientedProjectedPath, Int.cast_sub]
  congr 1
  ring

/-- Projecting a single oriented direction gives the sandpile step law. -/
theorem map_orientedProjectedStep_stepLaw :
    (stepLaw 2).map orientedProjectedStep = Sandpile.stepLaw 1 := by
  classical
  rw [stepLaw, Sandpile.stepLaw, LatticeProb.instructionLaw,
    Measure.map_smul _ (Measurable.of_discrete : Measurable orientedProjectedStep).aemeasurable,
    Measure.map_finset_sum' (Measurable.of_discrete : Measurable orientedProjectedStep).aemeasurable]
  simp only [Measure.map_dirac, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fintype.sum_bool]
  norm_num [orientedProjectedStep]
  simp only [← add_smul]
  have hc : (2 : ℕ) • (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    have h : (2 : ℝ≥0) * (4 : ℝ≥0)⁻¹ = (2 : ℝ≥0)⁻¹ := by norm_num
    have h' := congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) h
    simpa [nsmul_eq_mul] using h'
  rw [← two_nsmul, hc]
  abel

/-- The coordinate-difference path has the one-dimensional simple-walk law. -/
theorem map_orientedProjectedPath_walkLaw :
    (walkLaw 2).map orientedProjectedPath = Sandpile.walkLaw 1 0 := by
  have := stepLaw_isProbability (d := 2) (by norm_num)
  have hstep : Measurable orientedProjectedStep := Measurable.of_discrete
  have hmap : (walkLaw 2).map (fun p j => orientedProjectedStep (p j)) =
      Measure.infinitePi (fun _ : ℕ => Sandpile.stepLaw 1) := by
    rw [walkLaw, Measure.infinitePi_map_pi _ (fun _ => hstep)]
    simp only [map_orientedProjectedStep_stepLaw]
  have hpath : Measurable (Sandpile.walkPath (0 : Sandpile.Site 1)) := by
    apply Measurable.of_eval
    intro k
    unfold Sandpile.walkPath
    fun_prop
  rw [Sandpile.walkLaw, ← hmap, Measure.map_map hpath (by fun_prop)]
  congr 1
  funext p
  exact orientedProjectedPath_eq_walkPath p

end Parking
