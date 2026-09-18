/-
The Green potential and its decrement under one fresh direction.
-/
import Parking.Support.NearestGreen
import Parking.Support.RoundHitting
import LatticeProb.Walk.ExteriorDirichlet

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The Green function is bounded by its value at the origin. -/
theorem fullGreen_le_escapeConst (hd : 3 ≤ d) (x : Site d) : fullGreen d x ≤ escapeConst d := by
  have hg : 0 < escapeConst d := lt_of_lt_of_le zero_lt_one (one_le_escapeConst hd)
  apply (div_le_one hg).mp
  rw [fullGreen_div_escapeConst hd]
  exact srwHitProb_le_one (by omega) x

/-- One fresh walk step spends one unit of Green potential at the target. -/
theorem integral_step_green (hd : 3 ≤ d) (x y : Site d) :
    ∫ a, fullGreen d (x + stepVec a - y) ∂(stepLaw d) =
      fullGreen d (x - y) - if x = y then 1 else 0 := by
  have he : (fun a => fullGreen d (x + stepVec a - y)) =
      (fun a => fullGreen d ((x - y) + stepVec a)) := by
    funext a
    congr 1
    abel
  rw [he, integral_stepLaw_add (by omega)]
  have hg : fullGreen d = srwGreenInf d := funext fun z => fullGreen_eq_srwGreenInf d z
  rw [hg, walkOp_srwGreenInf hd]
  simp only [sub_eq_zero]

/-- A table entry has the one-step Green decrement, at any fixed entry. -/
theorem integral_table_green (hd : 3 ≤ d) (x y : Site d) (j : RoundSlot d) :
    ∫ τ, fullGreen d (x + stepVec (τ j) - y)
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) =
      fullGreen d (x - y) - if x = y then 1 else 0 := by
  haveI := stepLaw_isProbability (by omega : 1 ≤ d)
  have hm : (Measure.infinitePi fun _ : RoundSlot d => stepLaw d).map (fun τ => τ j) =
      stepLaw d := Measure.infinitePi_map_eval _ j
  calc
    _ = ∫ a, fullGreen d (x + stepVec a - y) ∂((Measure.infinitePi
        fun _ : RoundSlot d => stepLaw d).map (fun τ => τ j)) :=
      (integral_map (measurable_pi_apply j).aemeasurable
        (measurable_from_countable' _).aestronglyMeasurable).symm
    _ = _ := by rw [hm]; exact integral_step_green hd x y
end Parking
